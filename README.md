# kotoba-sema

`kotoba-sema` owns Kotoba source semantic analysis: reading forms, resolving
names, checking types and effects, elaborating capabilities, and producing a
validated HIR envelope.

```text
source bytes
  -> forms
  -> semantic analysis
  -> checked kotoba-hir
```

The implementation namespaces remain `kotoba.compiler.frontend`,
`kotoba.compiler.schema`, and `kotoba.compiler.kotoba-reader` during the
repository-boundary migration. Keeping those names preserves existing JVM and
NBB consumers while ownership moves out of the compiler orchestrator. New code
should enter through `kotoba.sema`.

The language repository remains authoritative for the vendored guest grammar
and capability catalog. This repository owns loading and enforcing those
contracts during semantic analysis.

`(eval request)` is deliberately not host evaluation. The frontend elaborates
the one-argument form to the catalogued `:code/eval` typed ability (wire ID 30),
inferring the request as `:document` and the result from its typed context.
`load-string`, `read-string`, reader evaluation, and ambient name resolution
remain forbidden. The host must resolve a checked definition CID and admit its
complete effect row before execution.

## Type-directed arithmetic (2026-09-02)

The plain numeric operators `+ - * / < <= > >= =` have one spelling each and
resolve by operand type, the way Unison resolves `+` to `Nat.+` or `Float.+`:

| operand types | `+` | `-` | `*` | `/` | `<` `<=` `>` `>=` | `=` | unary `-` |
|---|---|---|---|---|---|---|---|
| all `:i64` | `+` (unchanged) | `-` | `*` | rejected (use `quot`) | `<` ... | `=` | `-` |
| all `:f64` | `f64-add` | `f64-sub` | `f64-mul` | `f64-div` | `f64-lt` ... `f64-ge` | `f64-eq` | `f64-neg` |
| all `:f32` | `f32-add` | `f32-sub` | `f32-mul` | `f32-div` | `f32-lt` ... `f32-ge` | `f32-eq` | `f32-neg` |

- The resolution is a rewrite in the same type-directed pass that elaborates
  `option-or`, so it runs after variadic and chained forms are desugared to
  binary calls (`(< a b c)` on f64 lowers to two `f64-lt`) and before
  validation; every backend still sees only the typed operations.
- A program with no float operands is byte-identical to what it was before
  the rule existed (`test/kotoba/compiler/type_directed_arithmetic_test.clj`
  holds two integer programs beside their pre-change output).
- The explicit spellings (`f64-add`, `f32-lt`, ...) remain valid; typed and
  ABI boundaries may still name their operation exactly.
- `quot` and the bit operations are integer-only and are not overloaded.
- A decimal literal next to an `:f32` operand narrows exactly-or-refused,
  the same rule `(f32-add x 1.5)` already applies; `(+ x 0.1)` on f32 is
  refused, not rounded.
- An unannotated parameter used as `(+ p 1.5)` is refined to `:f64` by the
  same mechanism that refines a string parameter from `string-substring`.

**Invariant: there is no implicit numeric conversion.** An `:i64` next to an
`:f64`, or an `:f32` next to an `:f64`, is rejected with a message that names
both types and the explicit conversions the author must choose between:
`i64-to-f64-checked` / `i64-to-f64-rounded`, `f64-to-i64-checked` /
`f64-to-i64-truncating`, `i64-to-f32-checked` / `i64-to-f32-rounded`,
`f32-to-i64-checked` / `f32-to-i64-truncating`, `f32-to-f64-exact`,
`f64-to-f32-rounded`. Widening and narrowing each have two spellings because
overflow and rounding are decisions the source has to write down.

## Development

```sh
clojure -M:test
```

## Responsibility boundary

- Owns source reading and semantic admission.
- Owns source/schema diagnostics and source-to-HIR elaboration.
- Produces `kotoba-hir`; does not lower HIR to KIR.
- Does not orchestrate compilation or emit machine code.
