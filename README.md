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

## Development

```sh
clojure -M:test
```

## Responsibility boundary

- Owns source reading and semantic admission.
- Owns source/schema diagnostics and source-to-HIR elaboration.
- Produces `kotoba-hir`; does not lower HIR to KIR.
- Does not orchestrate compilation or emit machine code.
