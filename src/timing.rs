//! Per-argument timing. Clones share a record so lazy iterators and scope guards
//! can record measurements without keeping a mutable borrow alive.
use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet},
    rc::Rc,
    sync::OnceLock,
    time::Duration,
};

use quanta::Clock;

use crate::{Environment, Expr, RawExpr, TypeExpr, type_resolver::SymbolicTypeEnvironment};

fn clock() -> &'static Clock {
    static CLOCK: OnceLock<Clock> = OnceLock::new();
    CLOCK.get_or_init(Clock::new)
}

#[derive(Debug, Default)]
struct Measurements {
    enabled: bool,
    times: BTreeMap<&'static str, Duration>,
    vectors: BTreeMap<&'static str, Vec<Duration>>,
    environment_children: Vec<Duration>,
}

#[derive(Debug, Clone, Default)]
pub struct Timings {
    pub test_case: String,
    pub max_dimension: u64,
    measurements: Rc<RefCell<Measurements>>,
}

impl Timings {
    pub fn new(test_case: impl Into<String>, max_dimension: u64) -> Self {
        clock(); // Calibrate before starting any measurements.
        let timing = Self {
            test_case: test_case.into(),
            max_dimension,
            ..Self::default()
        };
        timing.set_enabled(true);
        for key in [
            "total_ms",
            "before_preprocessing_complete_ms",
            "after_preprocessing_complete_ms",
            "z3_integer_ms",
            "z3_real_ms",
        ] {
            timing.set_time(key, Duration::ZERO);
        }
        timing
            .measurements
            .borrow_mut()
            .vectors
            .insert("environment_processing_ms_by_max_dimension", Vec::new());
        timing
    }

    /// Default collectors are disabled; this can also be changed at runtime.
    pub fn set_enabled(&self, enabled: bool) {
        self.measurements.borrow_mut().enabled = enabled;
    }
    pub fn enabled(&self) -> bool {
        self.measurements.borrow().enabled
    }
    pub fn add_time(&self, name: &'static str, time: Duration) {
        let mut data = self.measurements.borrow_mut();
        if data.enabled {
            *data.times.entry(name).or_default() += time;
        }
    }
    pub fn set_time(&self, name: &'static str, time: Duration) {
        let mut data = self.measurements.borrow_mut();
        if data.enabled {
            data.times.insert(name, time);
        }
    }
    pub fn add_indexed_time(&self, name: &'static str, index: usize, time: Duration) {
        let mut data = self.measurements.borrow_mut();
        if data.enabled {
            let values = data.vectors.entry(name).or_default();
            if values.len() <= index {
                values.resize(index + 1, Duration::ZERO);
            }
            values[index] += time;
        }
    }
    pub fn times(&self) -> BTreeMap<&'static str, Duration> {
        self.measurements.borrow().times.clone()
    }
    pub fn vectors(&self) -> BTreeMap<&'static str, Vec<Duration>> {
        self.measurements.borrow().vectors.clone()
    }
    pub fn scope(&self, name: &'static str) -> Timer {
        Timer {
            timing: self.clone(),
            name,
            start: self.enabled().then(|| clock().raw()),
            index: None,
        }
    }
    pub fn check(&self, solver: &z3::Solver, arithmetic: &'static str) -> z3::SatResult {
        let _timer = self.scope(arithmetic);
        solver.check()
    }

    /// Nested environment scopes subtract child elapsed time from their own bin.
    pub fn environment(&self, environment: &Environment, types: &SymbolicTypeEnvironment) -> Timer {
        let mut timer = self.scope("environment_processing_ms_by_max_dimension");
        if timer.start.is_some() {
            let dimension = types
                .types
                .values()
                .map(|ty| structural_dimension(ty, environment))
                .max()
                .unwrap_or(0)
                .max(
                    environment
                        .natural_assignment
                        .iter()
                        .filter_map(|(parameter, value)| {
                            matches!(parameter, crate::NaturalParameter::ImplicitDimension(_))
                                .then_some(*value)
                        })
                        .max()
                        .unwrap_or(0),
                );
            timer.index = Some(usize::try_from(dimension).expect("dimension exceeds usize"));
            self.measurements
                .borrow_mut()
                .environment_children
                .push(Duration::ZERO);
        }
        timer
    }
}

fn structural_dimension(ty: &TypeExpr<()>, environment: &Environment) -> u64 {
    match ty {
        TypeExpr::Matrix(rows, cols) => environment
            .evaluate_natural(rows)
            .unwrap_or(0)
            .max(environment.evaluate_natural(cols).unwrap_or(0)),
        TypeExpr::Set(element) => structural_dimension(element, environment),
        TypeExpr::Seq(element, length) => {
            let length = environment.evaluate_natural(length).unwrap_or(0);
            let RawExpr::Type(element) = &element.raw else {
                return length;
            };
            (1..=length).fold(length, |largest, index| {
                let element = crate::type_expr::open_sequence_element(
                    element,
                    &Expr::new(RawExpr::NatLiteral(index)),
                );
                largest.max(structural_dimension(&element, environment))
            })
        }
        _ => 0,
    }
}

pub struct Timer {
    timing: Timings,
    name: &'static str,
    start: Option<u64>,
    index: Option<usize>,
}

impl Drop for Timer {
    fn drop(&mut self) {
        let Some(start) = self.start else {
            return;
        };
        let elapsed = clock().delta(start, clock().raw());
        if let Some(index) = self.index {
            let children = {
                let mut data = self.timing.measurements.borrow_mut();
                let children = data
                    .environment_children
                    .pop()
                    .expect("environment scopes must be nested");
                if let Some(parent) = data.environment_children.last_mut() {
                    *parent += elapsed;
                }
                children
            };
            self.timing
                .add_indexed_time(self.name, index, elapsed.saturating_sub(children));
        } else {
            self.timing.add_time(self.name, elapsed);
        }
    }
}

/// Each vector cell is a JSON array of milliseconds. The CSV crate handles its
/// quoting, including commas inside JSON and argument names.
pub fn to_csv(collectors: Vec<Timings>) -> Result<String, Box<dyn std::error::Error>> {
    let mut columns = BTreeSet::new();
    let mut vector_columns = BTreeSet::new();
    for timing in &collectors {
        let data = timing.measurements.borrow();
        columns.extend(data.times.keys().copied());
        columns.extend(data.vectors.keys().copied());
        vector_columns.extend(data.vectors.keys().copied());
    }
    let mut writer = csv::WriterBuilder::new()
        .has_headers(false)
        .from_writer(Vec::new());
    let mut header = vec!["test_case", "max_dimension"];
    header.extend(columns.iter().copied());
    writer.write_record(header)?;
    for timing in &collectors {
        let mut row = vec![timing.test_case.clone(), timing.max_dimension.to_string()];
        let data = timing.measurements.borrow();
        for name in &columns {
            if vector_columns.contains(name) {
                let values = data
                    .vectors
                    .get(name)
                    .into_iter()
                    .flatten()
                    .map(|duration| duration.as_secs_f64() * 1000.0)
                    .collect::<Vec<_>>();
                row.push(serde_json::to_string(&values)?);
            } else {
                row.push(
                    (data
                        .times
                        .get(name)
                        .copied()
                        .unwrap_or_default()
                        .as_secs_f64()
                        * 1000.0)
                        .to_string(),
                );
            }
        }
        writer.serialize(row)?;
    }
    Ok(String::from_utf8(writer.into_inner()?)?)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn accumulates_and_serializes_named_measurements() {
        let timing = Timings::new("a, \"quoted\" case", 2);
        timing.add_time("example_ms", Duration::from_millis(2));
        timing.add_time("example_ms", Duration::from_millis(3));
        assert_eq!(timing.times()["example_ms"], Duration::from_millis(5));
        timing.set_time("example_ms", Duration::from_millis(7));
        timing.add_indexed_time("bins", 2, Duration::from_millis(3));
        timing.add_indexed_time("bins", 2, Duration::from_millis(4));
        assert_eq!(
            timing.vectors()["bins"],
            vec![Duration::ZERO, Duration::ZERO, Duration::from_millis(7)]
        );
        let csv = to_csv(vec![timing]).unwrap();
        let mut reader = csv::Reader::from_reader(csv.as_bytes());
        let header = reader.headers().unwrap().clone();
        let row = reader.records().next().unwrap().unwrap();
        assert_eq!(&row[0], "a, \"quoted\" case");
        let bin_index = header.iter().position(|name| name == "bins").unwrap();
        assert_eq!(
            serde_json::from_str::<Vec<f64>>(&row[bin_index]).unwrap(),
            vec![0.0, 0.0, 7.0]
        );
    }
    #[test]
    fn disabled_collectors_do_not_accumulate() {
        let timing = Timings::default();
        timing.add_time("example", Duration::from_secs(1));
        timing.set_time("example", Duration::from_secs(1));
        timing.add_indexed_time("bins", 2, Duration::from_secs(1));
        drop(timing.scope("scope"));
        assert!(timing.times().is_empty());
        assert!(timing.vectors().is_empty());
        timing.set_enabled(true);
        timing.add_time("example", Duration::from_millis(7));
        timing.set_enabled(false);
        timing.set_time("example", Duration::from_millis(1));
        assert_eq!(timing.times()["example"], Duration::from_millis(7));
    }

    #[test]
    fn validation_records_phases_and_environment_buckets_on_early_returns() {
        use crate::validate_argument::{Arguments, ToFromMd};
        let mut arguments = Arguments::parse_str(
            r"# Dimensionless

Given:

- $x \in \mathbb{R}$

WTS $x = x$

# Symbolic matrix and nested environment

Given:

- $A \in \mathbb{R}^{n \times n}$

WTS $A = A$

1. Given:

   - $B \in \mathbb{R}^{2 \times 2}$

   WTS $B = B$

# Inconsistent shape

Given:

- $A \in \mathbb{R}^{2 \times 3}$
- $A = I$

WTS $A = A$

# Early preparation error

Given:

- $A \in \mathbb{R}^{2 \times 2}$
- $A + 1 = A$

WTS $A = A$

# Quantified vector

WTS $\forall x \in \mathbb{R}^{n}, x = x$

# Induction

WTS $n = n$ by induction on $n$

1. WTS $0 = 0$
2. Given:

   - $n = n$

   WTS $n + 1 = n + 1$

# Ellipsis synthesis

Given:

- $n = 2$
- $c \in \operatorname{Seq}_{n}(\mathbb{R})$
- $A = \operatorname{diag}(c_{1}, \ldots, c_{n})$

WTS $A = \operatorname{diag}(c)$",
        );
        let records = arguments.validate(2, &Timings::new("", 2));
        assert_eq!(records.len(), arguments.0.len());
        for (argument, record) in arguments.0.iter().zip(&records) {
            assert_eq!(record.test_case, argument.name);
            let times = record.times();
            for name in [
                "total_ms",
                "before_preprocessing_complete_ms",
                "after_preprocessing_complete_ms",
                "z3_integer_ms",
                "z3_real_ms",
            ] {
                assert!(times.contains_key(name));
            }
            assert!(
                times["before_preprocessing_complete_ms"]
                    + times["after_preprocessing_complete_ms"]
                    <= times["total_ms"]
            );
            let bucket_total: Duration =
                record.vectors()["environment_processing_ms_by_max_dimension"]
                    .iter()
                    .sum();
            assert!(bucket_total <= times["after_preprocessing_complete_ms"]);
        }
        assert_eq!(
            records[0].vectors()["environment_processing_ms_by_max_dimension"].len(),
            1
        );
        assert_eq!(
            records[1].vectors()["environment_processing_ms_by_max_dimension"].len(),
            3
        );
        assert!(records[2].vectors()["environment_processing_ms_by_max_dimension"].is_empty());
        assert!(records[3].vectors()["environment_processing_ms_by_max_dimension"].is_empty());
        assert_eq!(
            records[4].vectors()["environment_processing_ms_by_max_dimension"].len(),
            3
        );
        assert_eq!(
            records[6].vectors()["environment_processing_ms_by_max_dimension"].len(),
            3
        );
    }
}
