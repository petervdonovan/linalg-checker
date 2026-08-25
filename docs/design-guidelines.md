# Design Principles

## Preserve, Don't Recover

Carry structured information forward in the representation that owns it. Do not
render an expression and parse the resulting string to recover its structure,
erase metadata only to recompute it, or copy facts into side tables without a
clear ownership boundary.

In particular:

- symbolic result types belong in `TypedMetadata`;
- concrete natural assignments belong in `Environment`;
- generated obligations belong in `SideCondition`;
- source syntax remains an AST until the presentation boundary.

Avoid redundant representations. If two stored values can disagree, decide
which one is authoritative and derive the other when needed.

## Designing for Extensibility

Use visitors for syntax-wide behavior and ordered lowering passes for new
operators. A surface operator should usually add a focused desugaring visitor,
then disappear before dimension inference or Z3 lowering. An operator retained
in the stable core also needs an explicit type rule and compatibility handling.

Keep traversal policy in `Visit` or `VisitMut`; keep operator semantics in small
rules and visitors. Adding one operator should not require editing unrelated
recursive matches throughout the codebase.

## Keep Stages Honest

Each pipeline stage has one kind of authority:

- symbolic preparation determines symbolic types and exact rewrites;
- dimension inference enumerates natural assignments;
- concrete elaboration specializes environment-dependent operations;
- core lowering constructs Z3 values;
- workflow code decides what to assert and how to interpret solver results.

Do not make a later stage rediscover information an earlier stage should have
preserved. Do not let a lower-level helper silently apply workflow policy, such
as negating a counterexample query or deciding whether an existence assumption
is acceptable.

## Lower Toward a Small Core

Prefer exact, one-way desugaring over teaching every downstream subsystem every
surface construct. The core should be expressive enough to preserve semantics
but small enough that typing, dimensional compatibility, and Z3 construction
remain auditable.

Lowering must preserve meaning exactly. Approximate normalization and convenient
but stronger assumptions are not valid substitutes.

## Separate Symbolic and Concrete Facts

`TypeExpr` is the sole type representation. Matrix dimensions, sequence lengths,
and dependent sequence element types remain symbolic throughout the pipeline.
Do not introduce a parallel concrete type or duplicate types in `Environment`.
Evaluate only the required natural expressions against the selected assignment
when an operation needs a concrete size.

Lexically bound natural values belong in type expressions as bound leaves, not
in the environment assignment. Opening and abstraction must preserve their
scope rather than recovering it from variable names.

Hidden nonce dimensions identify occurrences; they are internal implementation
details and must not leak into user-facing TeX, Markdown, or models.

## Assumptions Define the Search Space

In argument validation, assumptions determine the base environments. A malformed
or unjustified step must not narrow the structures in which counterexamples are
sought. Step-local dimensional requirements are checked as extensions of each
base environment and reported when no extension exists.

This distinction is semantic, not an optimization detail.

## Make Failure Local and Explicit

Return structured errors where unsupported syntax, invalid typing, or impossible
dimensions are discovered. Panics are reserved for internal invariants, such as
conflicting authoritative annotations or impossible name collisions.

Do not preemptively hide failures with fallback semantics. An explicit error is
better than a plausible but incorrect Z3 query.

## Localize Errors Without Contagion

Attach a failure to the narrowest sentence responsible for it, discard that
sentence as a premise, and continue validating independent claims. A bad step in
a subproof does not make a correct conclusion wrong when the conclusion follows
from the remaining validated facts.

Keep the status of a conclusion separate from the quality of the justification
offered for it. Tree ancestry alone must never propagate failure.

## Test Semantics at the Right Boundary

Keep tests focused:

- direct TeX tests protect canonical rendering and grouping;
- preparation and elaboration tests inspect the corresponding AST boundary;
- lowering tests protect Z3 semantics;
- Markdown integration tests exercise complete user workflows.

Round trips may canonicalize, so they do not replace targeted rendering tests.
Avoid assumptions in examples that make the claimed result trivial; the system
should perform the reasoning the test is meant to demonstrate.
