# `validate_argument` examples

The two source corpora are deliberately kept as readable Markdown:

- [`successes.md`](successes.md) contains arguments the validator handles well, including realistic proofs with mistakes it catches.
- [`failures.md`](failures.md) contains representative limitations and surprising results found by trying nearby textbook proof variants.

Text surrounding the single inline mathematical claim on a proof step is ignored by the parser, so the source files can explain each step inline. The rendered diagnostic snapshots are [`successes.output.md`](successes.output.md) and [`failures.output.md`](failures.output.md).

Regenerate the snapshots with:

```text
UPDATE_EXPECT=1 cargo test --test validate_argument_examples
```

Normal runs of `cargo test --test validate_argument_examples` also write
`successes.output.timing.csv` and `failures.output.timing.csv` beside the Markdown
outputs. `cargo test --test validate_argument` writes
`tests/fixtures/validate_arguments_output.timing.csv`. These reports are gitignored
and overwritten on each run; snapshot updates are not needed to collect timing.

Each row identifies its argument by `test_case` and records the configured
`max_dimension`. All measurements are milliseconds. `total_ms` excludes parsing,
rendering, clock calibration, and file writing. The before/after preprocessing
columns split initial givens preparation from the remaining validation, including
lazy environment enumeration. Root induction work belongs to the after phase.

`z3_integer_ms` measures dimension and ellipsis-position solver checks;
`z3_real_ms` measures value and counterexample checks, including mixed arithmetic.
These overlap the phase totals. `environment_processing_ms_by_max_dimension`
contains a JSON array: index zero is dimensionless processing, and index d is
processing in environments whose largest matrix dimension or sequence length is
d. Nested processing is counted once. Enumeration and work outside environment
processing are included in the after total but need not appear in this array.

Library callers pass a `timing::Timings` collector to `validate`. A default
collector disables measurements; `Timings::new` enables them, and `set_enabled`
can switch collection at runtime. `Arguments::validate` returns one named
collector per argument, suitable for `timing::to_csv`.
