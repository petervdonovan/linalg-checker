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

`smt_backend::find_proof(context, conclusion, interpreter, limits)` searches for
n-ary conjunction introductions over whole visible contextual facts. It returns
one checked conclusion and a `Derivation` for the caller to record explicitly.
Assumptions and accepted external facts (including likely facts) are ordinary
leaves. The backend does not project conjuncts, consult elaborated alternatives,
expand archived proofs, or change ordinary argument validation.

`SearchLimits` supplies a bound on distinct reachable non-leaf proof values, a
premise-list capacity, and an optional timeout. Active slots form a distinct
prefix in canonical breadth-first first-encounter order, with the root in slot
zero. Repeated subproofs share a slot; references may point in either index
direction, and unreachable active slots are forbidden. Guarded child-reference
and discovery predicates implement `../../docs/symmetry-breaking.md`, using
O(a n²) constraints for n slots and premise capacity a. No node IDs are added.
Contextual reuse needs zero slots, even at zero premise capacity. Empty
introductions are not supported, and conjunction order/nesting are preserved.

The query uses `smt_dt::ProofDatatype` fragments for bounded structure and local
rule constraints. Models are evaluated and checked against the query before
being converted directly into existing local proof evidence. Selected leaf
references supply dependencies through the same constructor as ordinary rule
checking, followed by existing scope and witness-discharge bookkeeping. Failure
within the bounds, timeout, unknown, unsupported syntax, invalid analysis, and
inconsistent models have distinct errors. No proof is silently admitted.

See `snapshots/smt_backend.md` for found proofs and bounded failures, and
`../smt_dt/snapshots/proof_tree.smt2` for an actual datatype-only query. The generic
`smt_dt::selector_child` helper describes guarded immediate selector edges;
semantic proof-premise edges additionally traverse the bounded premise list.
