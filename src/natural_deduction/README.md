# One-step natural deduction

`follows_from_natural_deduction(context, written, interpreter, checks)` checks a
single principal inference with conjunction preparation against the visible context. The interpreter resolves the
new occurrence in its lexical scope. The returned established result contains
both its `CheckedFormula` and derivation proposals; acceptance uses that checked
conclusion directly. Facts accepted as verified or likely are equally available.

The supported rules are existential introduction, witness opening, universal
introduction/elimination, implication introduction, conjunction introduction/elimination,
and contextual reuse. Conjunction premises may be assembled from contextual views;
missing premises are not proved by another implication or quantifier rule. Dimension evidence retains scope dependencies
without propagating verification statuses.

## Immutable interpretations

`CheckedFormula` has private contents and is created only by successful central
formula analysis. It keeps the written expression, an analyzed interpreted
meaning, and the identities/types of its free parameters. The natural deduction
context accepts checked formulas and checked alternatives, never optional analysis.

Contextual surface interpretation (including ellipses) precedes matching and
preserves logical quantifiers. Identical text in a stronger local scope can acquire
a different meaning and must be justified again. Reuse compares frozen meanings;
the proof records whether it is a literal repetition or a resolved contextual view.

Concrete lowering is a separate consumer. The validator's append-only cache is
keyed by interpretation identity, including unsupported-lowering results. It lowers
frozen meanings without resynthesizing contextual notation. Child occurrences and
automatic implication exports cannot overwrite a parent's prepared interpretation.

## Bindings and acceptance

Typed formulas retain lexical quantifier bindings. Capture-safe renaming reserves
all names, including names in type annotations, and respects sequence and set
binders. Domains and endpoints use the outer scope; bodies use their own binding.
Value annotations are reconstructed from frozen lexical free types and saved
binder maps, rather than re-inferring binders against a later context.

Checking is read-only. Witness candidates are first interpreted in provisional
typing scopes and rematched against the selected source. Acceptance explicitly
chooses the first suitable source and commits one opening. Failed checks and
foreign proof references cannot partially register assumptions or witnesses.

Witness discharge replaces the local payload assumption with the source
existential's dependencies when its variables are absent from the conclusion,
remaining assumptions, and dependent types. Goals use the same inference rules;
a locally valid witness-bearing conclusion may be ineligible for export.

## Shared storage and scoped visibility

Each root owns an append-only `ProofStore` shared through `Rc` by child contexts.
Immutable fact contents and derivations are stored once. Contexts clone only their
visibility/active-derivation handles and scoped typing state. Inspecting a stored
proof does not make it available as a premise in another scope.

Scope exit creates an `ExportDelta` containing newly eligible facts/derivations,
excluding unchanged inherited entries. Applying it updates visibility without
copying or reregistering records. Superseded derivations remain inspectable through
stable IDs. Deltas and checked formulas from another root store are rejected.

Assumption dependencies describe scope only. Independent facts from failed goals
may export; facts requiring local assumptions or free parameters remain local.
Externally checked SMT facts retain the existing conservative dependency policy.

## Local evidence and rendering

`ProofInput` distinguishes contextual leaves from intermediate conclusions and
local rule applications. Conjunction projections record immediate operand indices;
nested projections form explicit elimination chains. Conjunction introduction
preserves operand order and nesting. Neither operation admits intermediate facts.
`ReuseKind` distinguishes literal repetitions, resolved meanings, and checked
elaborated views rather than using a conjunction projection as generic reuse.

`NaturalDeductionProof::to_tex(conclusion)` renders a math-mode proof tree, and
`details(conclusion)` provides shared Markdown explanations plus that tree,
omitting trees consisting only of literal or resolved contextual reuse. Neither
operation accesses the proof store: contextual facts remain leaves even when their
archived proofs are long. Discharged formulas are saved with the local evidence
and assigned deterministic presentation labels. The validator supplies summaries,
HTML wrappers, and validation-specific warnings only. A final elaborated view is
shown explicitly, including when a witness proves an existential equivalent to a
surface membership statement.

## Standalone SMT proof search

`smt_backend::find_proof(context, conclusion, interpreter, limits, timings)` searches
for conjunction introduction/elimination and implication introduction over visible
contextual sources and temporary assumptions. It returns one checked conclusion and a `Derivation` for
the caller to record explicitly. Every visible nondominated contextual derivation
has its own source identity; equal formulas do not erase assumption identities or
dependency alternatives. Accepted external facts, including likely facts, remain
available without propagating verification qualifications.

Ambient assumption leaves carry existing assumption identities; established leaves
carry contextual derivation references and their recorded dependencies. Temporary
leaves have query-local identities with symbolic formulas. There are at most as
many temporary identities as inference slots, each reusable at several leaves.
Assumptions and established facts consume no slots. The backend does not consult elaborated alternatives, expand archived proofs, or change
ordinary argument validation.

`SearchLimits` supplies a bound on distinct reachable non-leaf proof values, a
premise-list capacity, and an optional timeout. Active slots form a distinct
prefix in canonical breadth-first first-encounter order, with the root in slot
zero. Repeated subproofs share a slot; references may point in either index
direction, and unreachable active slots are forbidden. Guarded child-reference
and discovery predicates implement `../../docs/symmetry-breaking.md`, using
O(a n²) constraints for n slots and premise capacity a. No node IDs are added.
Contextual reuse needs zero slots, even at zero premise capacity. Empty
introductions are not supported, and conjunction order/nesting are preserved.

Each slot and the root have exact Boolean dependency vectors over ambient and
temporary assumption identities. Conjunction introduction unions premise sets;
conjunction elimination copies its whole premise dependency set unchanged;
implication introduction removes the used assumptions whose encoded formula
matches its whole antecedent. Discharge is local to the resulting node, and
vacuous discharge is permitted. Conjunction antecedents require explicit elimination
nodes to project their components. Temporary formulas used by a proof are checked as Boolean in
the existing typing context; no parameters or context facts are created.

`SearchLimits::max_root_dependencies` bounds the number of true ambient root bits,
not vector width. `None` is unrestricted, and `Some(0)` requires no remaining open
assumptions. All temporary root bits are always false. A pure Boolean sequential
counter implements the bound, retaining QF_DT. The selected root set is read from
the model, not prescribed or minimized automatically. A caller can repeat searches
with smaller bounds while retaining the same proof-size and premise limits.

`SearchLimits::max_finop_arity` is independent of `max_premises`: elimination
consumes one proof premise even when the conjunction contains many operands. A
single elimination rule selects any immediate operand; nested projection needs
multiple steps. Empty conjunctions have no eliminations. Decoding retains the
first matching operand index as evidence, without separate left/right rules.

Search uses `ExprDatatype::with_max_finop_arity`, whose capacity-indexed cons-list
sorts structurally bound every `Finite` application (Plus, Times, And, Or) at any
expression depth. Oversized input formulas produce an explicit encoding error;
symbolic terms cannot evade the bound in nested expressions. Matrix cells,
sequence elements, and quantifier premises keep their separate list sorts.
`ExprDatatype::new` remains available for unbounded structural encoding, while
the complete proof-rule constraint builder requires a bounded codec.

Generated formulas remain arbitrary expressions. No expression-height bound or
relevant-formula restriction is imposed. Existing context parameters are registered
for decoding new predicates even when absent from input facts. Every decoded
inference conclusion is checked by the central formula analyzer. A structurally
satisfiable query can therefore return `InvalidModel` for an ill-typed or otherwise
unsupported generated term, even if another valid model exists. There is no
model-blocking/retry loop, and this outcome is not a bounded non-derivability result.

The query uses `smt_dt::ProofDatatype` fragments for bounded structure and local
rule constraints. Models are checked against the assertions, and dependencies are
independently replayed while decoding the local proof. Source references and scope
requirements remain explicit. The returned dependency set exactly matches the
model: `find_proof` does not apply post-solve witness discharge. Explicit context
recording retains its existing witness-discharge alternatives. Failure within the
bounds, timeout, unknown, unsupported syntax, invalid analysis, and inconsistent
models have distinct errors. No proof is silently admitted.

Nested proof rendering assigns stable local discharge labels, scoped to ancestor
introductions; sibling branches cannot discharge each other's uses. It continues
to use display fractions and to omit trivial contextual-reuse trees.

See `snapshots/smt_backend.md` for found proofs and bounded failures, and
`../smt_dt/snapshots/proof_tree.smt2` for an actual datatype-only query.
`snapshots/implication_query.smt2` also shows the dependency vectors and root bound. The generic
`smt_dt::selector_child` helper describes guarded immediate selector edges;
semantic proof-premise edges additionally traverse the bounded premise list.

Both snapshot tests write an adjacent ignored `.timing.csv` on every run, using
the existing timing collector and CSV format. `local_proofs.timing.csv` measures
only deduction checks. `smt_backend.timing.csv` separates total search time,
analysis/query construction (`query_ms`), solver checks (`z3_dt_ms`), and model
extraction/validation/decoding (`decode_ms`). Context setup, replay, and rendering
are excluded. These checks do not enumerate dimensions, so `max_dimension` is 0;
proof bounds remain documented in the Markdown cases. Pass a default disabled
`Timings` collector when measurements are not needed.
