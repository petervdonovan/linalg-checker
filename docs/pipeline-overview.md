**Pipeline Overview**

1. Parse into `Expr<()>`.
2. Infer variable types into `SymbolicTypeEnvironment`.
3. Clone into `Expr<TypedMetadata>` and resolve symbolic node types.
4. Run desugaring visitors, producing rewritten expressions and `SideCondition`s.
5. Resolve types again using core operator rules.
6. Generate dimensional constraints and enumerate concrete `Environment`s.
7. Lower a `PreparedExpression` under one concrete environment to Z3.
8. Assert side-condition definitions and solve.

**Expression Metadata**

[TypedMetadata](/home/peter/school/leantutor/linalg-checker/src/type_resolver.rs:31) contains:

```rust
Option<TypeExpr<()>>
```

It stores the symbolic value type of each expression node. Examples:

- `A`: `Matrix(A_rows, A_cols)`
- `A B`: `Matrix(A_rows, B_cols)`
- `x + y`: the symbolic scalar least upper bound
- comparison: `Bool`

It does not store:

- Concrete dimensions.
- Variable declarations.
- Z3 expressions.
- Dimension constraints.
- Side conditions.
- Logical polarity.
- Source locations.

`TypeExpr` dimension expressions themselves have `()` metadata. Therefore metadata records a node’s symbolic result type, but does not recursively type the expressions appearing inside that type.

**Variable Types**

[SymbolicTypeEnvironment](/home/peter/school/leantutor/linalg-checker/src/type_resolver.rs:209) is the authoritative mapping:

```rust
Variable -> TypeExpr<()>
```

It comes from explicit memberships, natural-variable usage, and name-based guesses. `TypeResolver` uses this for variable leaves and writes resulting types into node metadata.

Lexically bound sequence indices are kept separately in `TypeResolver::lexical_types`. They are temporary traversal state and never enter the global symbolic environment.

**Operator Rules**

`OperatorTypeRules` contains the functions that calculate parent types from child types.

Each rule receives temporary `TypeRuleOperand`s containing:

- The child’s resolved value type, when it has one.
- A metadata-free snapshot of the child syntax.

The syntax snapshot supports rules such as casts and subscripts. It is not used to recover child types: those are passed explicitly through `value_type`.

**Visitor Context**

[VisitContext](/home/peter/school/leantutor/linalg-checker/src/visit_mut.rs:29) carries `logical_polarity` top-down during traversal.

Polarity is not stored in node metadata. `PreparedExpression.context` retains it afterward as provenance so callers can verify that positive and negative preparations are used correctly.

**Desugaring Results**

[PreparedExpression](/home/peter/school/leantutor/linalg-checker/src/preprocessing.rs:12) carries three things between preprocessing and later stages:

```rust
expression: Expr<TypedMetadata>
side_conditions: Vec<SideCondition<TypedMetadata>>
context: VisitContext
```

A `SideCondition` explicitly carries information that cannot live on one rewritten node:

- Introduced synthetic variable.
- User-facing display name.
- Symbolic introduced type.
- Defining assertions.
- Existence classification and checkable assertions.

Synthetic variable types temporarily extend the type lookup during the second type-resolution pass.

**Why Type Resolution Runs Twice**

The first pass types surface syntax so visitors can distinguish scalar and matrix operations.

Visitors then introduce new core expressions and synthetic variables. The second pass validates and types that rewritten core syntax. Some visitor-created nodes are provisionally typed, but the second pass is authoritative for the completed tree.

This is intentional recomputation, though it is one place where future cleanup may separate construction-time annotations from final validation more clearly.

**Dimension Inference**

Dimension inference reads symbolic types from node metadata, but stores its working information separately:

- `Shape`: solver-backed scalar, matrix, or sequence shape.
- `natural_symbols`: dimension variable to Z3 integer.
- `implicit_dimensions`: nonce to Z3 integer.
- `projections`: metadata-free expression to Z3 integer.
- The Z3 solver itself: compatibility, positivity, and ordering constraints.

Constraints are asserted directly into the solver. There is no dimension-constraint IR.

`ConstraintMode` is temporary builder state controlling whether constraints are permanent or contextual. It is not attached to expressions or individual constraints.

**Concrete Environments**

A yielded [Environment](/home/peter/school/leantutor/linalg-checker/src/lib.rs:143) contains:

```rust
types: Variable -> Type
equalities: Expr<()> -> u64
implicit_dimensions: ImplicitDimension -> u64
```

These are model-dependent facts and therefore should not be expression metadata.

`equalities` supplies concrete values needed for:

- Symbolic power exponents.
- Sequence bounds.
- Symbolic cast dimensions.
- Basis-vector indices and other projections.

Metadata-free keys are intentional here: metadata must not affect whether two environment-dependent expressions denote the same projection.

**Z3 Boundary**

[to_z3](/home/peter/school/leantutor/linalg-checker/src/to_z3.rs:460) receives:

- A typed, preprocessed expression.
- Its symbolic side conditions.
- One concrete environment.

It temporarily extends the concrete environment with synthetic variable types and returns:

```rust
ToZ3Result {
    expression: Z3Object,
    side_conditions: Vec<LoweredSideCondition>,
}
```

The lowered side conditions retain definitions and existence classifications. Model-finding callers assert definitions explicitly and handle existence warnings separately.

Synthetic variables are omitted from extracted user models because model extraction iterates over `Environment::types`, not the private extended lowering environment.
