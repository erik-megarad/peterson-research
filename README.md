# Peterson Research

Peterson Research is a growing collection of Lean formalizations and
reconstructions of Gary L. Peterson's research. It aims to make the ideas and
arguments in his papers understandable and inspectable, with explanations
linked to proofs checked by Lean. Each paper keeps its own source account,
model assumptions, checked results and open questions.

The collection covers five papers, including work with Michael J. Fischer and James E. Burns. Each reading path distinguishes checked positive results, counterexamples and unestablished claims.

Choose a reading path:

- [Essential Dekker](docs/essential-dekker.md): repeated two-process safety and
  request service, arbitrarily many finite overtakes, the printed generalization's
  obstruction, and safety with starvation after an explicitly selected correction.
- [Economical solutions](docs/economical-solutions.md): Algorithms 1/2 and 5/6
  safety and request service; 5/6 FIFO and doorway termination; clock and
  Algorithm 7 counterexamples; register counts, a failure-model lower bound,
  and initialized solo work.

- [Circular extrema election](docs/circular-election.md): maximum-owner announcement, fair eventual election and a bound on actual sends through first announcement.
- [Concurrent Reading While Writing](docs/concurrent-reading.md): intact returned samples, actual-write provenance, a common order per finite history and conditional own-operation completion.
- [Multi-reader atomic values](docs/multi-reader-atomic.md): two checked atomicity counterexamples for the normalized Figure 1 reconstruction, with separate provenance and own-completion results. This is a mixed-result reconstruction.

The papers retain distinct memory and scheduling assumptions. The register papers use different primitive contracts: overlapping raw buffers with atomic controls in concurrent reading, and regular registers including controls in multi-reader atomic values. There is no composition theorem between them. The guides place assumptions and limits beside each result.

The [exact declaration index](docs/claims.md) connects the explanations to Lean.
The [verification guide](docs/verification.md) explains reproduction, pins and
trust limits. [STATUS](STATUS.md) distinguishes completed research from release
qualification. Machine-readable claim records and a file-hash manifest are in
[corpus/records.jsonl](corpus/records.jsonl) and
[corpus/manifest.json](corpus/manifest.json). The [bibliography](corpus/bibliography.bib)
identifies the sources; their PDFs and transcriptions are not distributed.

Peterson's 1981 mutual-exclusion algorithm has a separate
[core repository](https://github.com/erik-megarad/peterson-algorithm), reflecting
its central place in his work. It contains the completed formalization and
explanations for that algorithm. The shared Lean root here makes the current
collection convenient to build and explore; each paper retains its own semantics.

## AI assistance

Erik Peterson started and directs the project. Its formalizations, proof
attempts and explanations are model-generated, with separate AI agents
reviewing source/model boundaries and completed proof paths. Lean's kernel
checks proof terms; source faithfulness relies on the documented reviews.
The source-specific guides disclose interpretation and version gaps.

Project material is offered under the [MIT license](LICENSE) for applicable
rights. That license does not cover the source papers or fetched dependencies.
Use [CITATION.cff](CITATION.cff) to cite the collection and cite the original paper authors separately for their work. No author-confirmed erratum,
novelty claim or upstream-library acceptance is implied.
