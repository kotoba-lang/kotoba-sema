# Higher-order guest callable candidate

A callable clause may take or return another guest callable. Logical `[:fn ...]`
contracts stay separate from physical i64 closure words: helpers and dispatchers
carry callable parameter/result metadata, choose families using logical contracts,
and retain closure refinements. This does not make raw JavaScript values callable.
Linear resources, existing type/arity/capture limits and allocation ledgers remain
checked. Ordinary integer closure controls retain their exact HIR bytes.

This is a candidate, not a published language/runtime qualification. The prepared vendored copy matches the higher-order authority candidate at
2eb28eabdcf9648069a60976afc300219320cf10a42ee71f55e8df925e7e5212. Publication
requires the authority main resync before this candidate merges and the consumer
pin advances. The normal Amu
pipeline still uses published Sema 60a1b0e and refuses this source with exit 65.
The direct pipeline result below cannot replace that normal qualification.

`source-qualification.json` records the unchanged maintained tests plus new cases,
a fresh b379f35 source baseline, identical integer HIR, and direct checked
Sema -> published Osaho -> published Script -> offline Node runtime evidence.
The direct runtime preserves 112 opaque identities, performs zero Proxy reads,
checks 2,000 **fresh instances**, and retains fuel/allocation traps (the latter
stops after 1,024 higher-order calls). This does not prove unbounded callbacks,
escaping host callables, reentrancy, async callbacks, or full harness parity.

The older typed-parameter diagnostic has the same two historical rendering-golden
failures on the baseline and candidate. Those goldens are preserved. New callable
parameter admission replaces the corresponding former refusal test with execution;
linear-resource refusal remains tested.

System One's public status returned HTTP 503. There was no model attempt for this
candidate; the source is an operator change. Exact commit CI and main publication
are separate gates and are not claimed here.

The synchronized Node gate runs 40 tests / 219 assertions. Three new portable
contract tests check actual vendored bytes, callable metadata/limits and aggregate/
per-definition source bounds. Against the old b379 grammar bytes the same gate
has nine failures. The existing definition-admission tests separately pass 2/4.

CI audit: the prior JVM job completed with **0 tests / 0 assertions**. Its success
is not source coverage or Q9 qualification. The opaque-js-bootstrap job actually
ran 37/207 before this resync; this change puts the grammar contract in that real
fixed-count Node gate. The historical JVM-only vendor check shares its digest
with the portable test rather than maintaining another literal.
