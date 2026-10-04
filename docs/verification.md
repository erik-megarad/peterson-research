# Reproduce and interpret the checks

The repository is one Lean project with source-specific namespaces. The
[toolchain file](../lean-toolchain) pins Lean `v4.35.0-rc3`; the
[Lake configuration](../lakefile.lean) pins CSLib commit
`9a99cbb320aa7742ecbbcecb8df6b404a9b587a3`. The
[dependency manifest](../lake-manifest.json) fixes the resolved graph. Use
those pins; a different installed toolchain is not equivalent evidence.

With the Lean toolchain manager installed, run from the repository root:

```sh
lake build Peterson CircularElection ConcurrentReading MultiReaderAtomic
```

The root library builds the exported modules. To inspect particular statements
and their logical assumptions, a temporary file in the root can contain:

```lean
import Peterson.EssentialDekker.TwoProcessProgressProof
import Peterson.EconomicalSolutions.Algorithm7LevelOne
import Peterson.EconomicalSolutions.TwoStateBypass

#check Peterson.EssentialDekker.TwoProcess.Progress.request_eventually_entry
#print axioms Peterson.EssentialDekker.TwoProcess.Progress.request_eventually_entry
#check EconomicalSolutions.Algorithm7.LevelOneCounterexample.level_one_starvation
#print axioms EconomicalSolutions.TwoState.Program.binary_impossibility
```

Save it as `Inspect.lean`, run `lake env lean Inspect.lean`, then remove it.
The [declaration index](claims.md) supplies the other modules and names.
[publication-checks.toml](../publication-checks.toml) is the exact release
contract: every checked claim record names a module and declaration set;
its source list covers all exported Lean files.

A successful build checks the encoded statements using Lean's kernel. Release
qualification also rejects proof placeholders, unintended custom axioms and
prohibited escape hatches in claimed paths, and checks theorem-kind and axiom
reports for every contract declaration. Only `propext`, `Classical.choice` and
`Quot.sound` are permitted; a theorem may use a subset. The ordinary `lake build`
command is not by itself the entire release screening procedure.

The original research was independently reviewed by AI agents for the
source/model connection, and its clean checks reused dependency caches. Public
qualification is a separate check of this exported layout. Neither a compiler
nor a content hash can show that a paper intended a particular scan order,
failure model or outline expansion. The guides disclose those boundaries.
There is no claim of independent human mathematical review or a second kernel
implementation checking this collection.

The [manifest](../corpus/manifest.json) binds paths, hashes and rights classes;
[SOURCE_REVISION](../SOURCE_REVISION) identifies the authoritative source
snapshot. The corpus [records](../corpus/records.jsonl) retain assumptions,
non-goals, source citations and evidence categories. No source PDF, OCR,
transcription, private research note or dependency source is redistributed.
External dependencies retain their own licenses when fetched.

For unchanged release inputs, existing successful qualification can be reused
with exact input and output comparison. Repeated compilation is not additional
source-faithfulness evidence. Changed proofs, pins or claim contracts require
fresh matching qualification before release.

## Combined graph and source compatibility

The original two-paper collection used Lean 4.34.0-rc2 and CSLib `33e7370a94646c19176dc847f7514559bc5e06fb`. The new register developments use Lean 4.35.0-rc3 and CSLib `9a99cbb320aa7742ecbbcecb8df6b404a9b587a3`; circular election used that compiler with CSLib `8c41993c70ae56d3138ad27254aba3887169b5dc`. This collection selects the register graph as its single root. Authoritative sources retain their original bytes and pins. Thirty-eight legacy modules receive a guarded module-system wrapper in this exported consumer: `module`, `public import` for each original import, and `@[expose] public section` before the exact original declaration body. This preserves the intended public names and unfoldable definitions; compiled API compatibility is established only by the actual candidate qualification. One additional module, Algorithm5Erasure, changes only the final proof tactic of `erasure_observation` from `by decide` to `by decide +kernel`. Its original finite heartbeat limit of 800000 is retained. Definitions and complete theorem statements remain byte-identical. This explicitly disclosed proof-elaboration change replaces the unsuccessful higher-heartbeat experiment.

Private development checks under their own pins do not qualify this combined graph. The changed graph, added libraries and expanded claim contract require fresh qualification of the actual assembled root. Successful release evidence must bind that qualification to the candidate bytes; this guide does not assert a build result. The root has four explicit default library targets, so `lake build` also builds all selected libraries.

To inspect the new statements after building the root:

```sh
lake env lean CircularElection/Targets.lean
lake env lean ConcurrentReading/Targets.lean
lake env lean MultiReaderAtomic/Targets.lean
```

Those files state targets; the complete library build checks their selected proofs. The exact new declarations are linked from the [claim index](claims.md). For example an inspection file can import `MultiReaderAtomic.RestrictedCounterexample` and issue `#print axioms MultiReaderAtomic.regularFc_not_restrictedFiniteCorrectness`; it reports logical dependencies of that negative theorem, not positive atomicity.

### Guarded consumer compatibility

The first combined-root check failed on fourteen legacy files importing module-system Mathlib modules and on Algorithm5Erasure's local elaboration budget. A second attempt exposed a separate Lean rule: a module cannot import a non-module dependency. The consumer wrapper therefore covers the exact 38-file local dependency closure of those fourteen files, adding 24 dependency modules. It retains original import order with public imports and an exposed public section, preserving all original declaration bodies and explicit private modifiers. This is a dependency closure, not a migration of every importer: 34 other legacy files remain exact copies, and Algorithm5Erasure receives only its named kernel-decision tactic adjustment. Warning and trust checks remain enabled.

Each adapted copy in the manifest records its named profile and the original input SHA-256, while the file SHA-256 binds the resulting consumer bytes. The module adaptation adds only the wrapper and `public` import prefixes; the current A5 adaptation adds `+kernel` only to the terminal tactic of the named theorem. This routes the decision proof through Lean's kernel instead of the elaborator's expensive weak-head reduction; it does not use native evaluation or add a trusted computation axiom. The adapted combined root passed qualification of all 93 named theorem endpoints with only the permitted standard axioms, and every reader command above passed. These checks reused the retained root and locked dependency sources and compiled artifacts; they are not a dependency-cold build. The successful report is reusable only for identical proof inputs and checker implementation. Source hashes are mandatory and a changed input, unexpected import layout, unsupported profile or unapproved module path fails closed. This is generated assembly rather than a second maintained proof implementation. The source snapshot still identifies the authoritative original inputs. Kernel and exact-axiom qualification must check this adapted graph; static source comparison alone is not a compiled-API verdict.
