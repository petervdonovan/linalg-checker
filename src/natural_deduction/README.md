# One-step natural deduction

`follows_from_natural_deduction(context, conclusion, checks)` checks whether a
statement follows in one supported step from the accepted context. It does not
establish the global truth of its premises. Facts accepted as either verified or
likely are equally available to the rules; a successful inference is verified.

The rules are existential introduction, existential witness opening, universal
introduction, universal elimination, implication introduction, and contextual
reuse. Conjunct projections and elaborated alternatives retain their source
provenance. Missing premises are not proved recursively. No match is not a
counterexample, and inconclusive side conditions are distinguished from failure.

## Typing and context

`ProofContext` owns the authoritative symbolic typing environment and scoped facts.
`type_resolver::analyze_formula` checks surface formulas without requiring SMT
lowering. Quantifiers, including restrictions, multiple binders, and quantified
Boolean operands, use the same analysis as ordinary formulas. Typed expressions
retain their lexical binder resolution. Later declarations cannot reinterpret
binders in an earlier fact; matching alpha-renames stored binders when needed.

Concrete SMT environments are assignments for individual fallback checks. They
are not a second symbolic context. Validation walks statements in order, tries
natural deduction, and otherwise aggregates the statement's fallback results
before accepting its original symbolic formula. One successful concrete case
cannot admit a fact that fails in another case.

The deduction engine performs no SMT proof search. `SideConditionChecker` can
establish symbolic type and dimension compatibility, but cannot prove missing
logical premises. Finite dimension sampling does not certify those conditions.
Accepted natural-number constraints can support dimension checks; their derivation
references and scope dependencies are retained as side-condition evidence.
Well-definedness obligations are checked separately from the inference itself;
unresolved obligations are not relabeled as a likely natural deduction proof.

## Assumptions, witnesses, and export

Assumption and parameter dependencies describe scope, not recursive verification
status. Distinct occurrences of the same assumption have distinct IDs. Alternative
derivations with incomparable scope dependencies are retained. External SMT facts
conservatively depend on all active assumptions and parameters.

Checking is read-only. Acceptance selects the first suitable witness source
explicitly and commits a single opening, or records the nondominated ordinary
proof alternatives. Opening a witness registers its parameter and local payload
assumption, linked to the chosen existential fact. Discharge replaces that
assumption with the source's dependencies when the witness is absent from the
conclusion, remaining assumptions, and dependent types.

Goals use the same inference rules as statements. A witness-bearing goal can be
verified locally without being exportable. Both automatic implication/universal
exports and independent internal facts must satisfy the parent scope's assumption
and free-parameter requirements. Witnesses are never generalized automatically.
Independent facts from a failed goal remain eligible for export.

The validator preserves the prepared interpretation of accepted ordinary facts,
including ellipses interpreted under local givens. Solver reconstruction reuses
that interpretation rather than reinterpreting surface text in another scope.

The proof API contains no solver trackers, finite-validation qualifications, or
Markdown nodes. SMT bounds describe only the particular fallback result that
used them; they do not propagate through subsequent natural deduction steps.
