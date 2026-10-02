# `validate_argument` examples

The two source corpora are deliberately kept as readable Markdown:

- [`successes.md`](successes.md) contains arguments the validator handles well, including realistic proofs with mistakes it catches.
- [`failures.md`](failures.md) contains representative limitations and surprising results found by trying nearby textbook proof variants.

Text surrounding the single inline mathematical claim on a proof step is ignored by the parser, so the source files can explain each step inline. The rendered diagnostic snapshots are [`successes.output.md`](successes.output.md) and [`failures.output.md`](failures.output.md).

Regenerate the snapshots with:

```text
UPDATE_EXPECT=1 cargo test --test validate_argument_examples
```
