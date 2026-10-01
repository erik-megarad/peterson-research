# Reproduce and interpret the checks

The repository is one Lean project with source-specific namespaces. The
[toolchain file](../lean-toolchain) pins Lean `v4.34.0-rc2`; the
[Lake configuration](../lakefile.lean) pins CSLib commit
`33e7370a94646c19176dc847f7514559bc5e06fb`. The
[dependency manifest](../lake-manifest.json) fixes the resolved graph. Use
those pins; a different installed toolchain is not equivalent evidence.

With the Lean toolchain manager installed, run from the repository root:

```sh
lake build Peterson
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
