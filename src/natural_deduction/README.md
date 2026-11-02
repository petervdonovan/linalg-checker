# One-step natural deduction

`follows_from_natural_deduction(context, written, interpreter, checks)` checks a
single rule application against the visible context. The interpreter resolves the
new occurrence in its lexical scope. The returned established result contains
both its `CheckedFormula` and derivation proposals; acceptance uses that checked
conclusion directly. Facts accepted as verified or likely are equally available.

The supported rules are existential introduction, witness opening, universal
introduction/elimination, implication introduction, and contextual reuse. Missing
premises are not proved recursively. Dimension evidence retains scope dependencies
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
