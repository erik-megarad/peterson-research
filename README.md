# Peterson Research

Peterson Research is a growing collection of Lean formalizations and
reconstructions of Gary L. Peterson's research. It aims to make the ideas and
arguments in his papers understandable and inspectable, with explanations
linked to proofs checked by Lean. Each paper keeps its own source account,
model assumptions, checked results and open questions.

Peterson's 1981 mutual-exclusion algorithm has a separate
[core repository](https://github.com/erik-megarad/peterson-algorithm). It
contains the completed formalization and explanations for that algorithm. The
shared Lean root here makes the current collection convenient to build and
explore; each paper retains its own semantics.

The first two papers are *The Essential Dekker's Algorithm* and, with Michael
J. Fischer, *Economical Solutions for the Critical Section Problem in a
Distributed System*. They begin a broader collection; future additions will
have their own reviewed scope. These first entries include both successful
guarantees and counterexamples: a safe algorithm can still leave someone
waiting forever.

Start with either of the first two reading paths:

- [Essential Dekker](docs/essential-dekker.md): repeated two-process safety and
  request service, arbitrarily many finite overtakes, the printed generalization's
  obstruction, and safety with starvation after an explicitly selected correction.
- [Economical solutions](docs/economical-solutions.md): Algorithms 1/2 and 5/6
  safety and request service; 5/6 FIFO and doorway termination; clock and
  Algorithm 7 counterexamples; register counts, a failure-model lower bound,
  and initialized solo work.

The current papers use distinct mathematical models. Dekker uses protocol
fairness and critical completion; economical solutions additionally model automatic reset
and request abortion on failure. Both interleave individual atomic shared
accesses. Neither establishes weak-memory correctness, an executable
implementation, or a wall-clock guarantee. The guides put the additional
assumptions beside each result and preserve the claims that remain unestablished.

The [exact declaration index](docs/claims.md) connects the explanations to Lean.
The [verification guide](docs/verification.md) explains reproduction, pins and
trust limits. [STATUS](STATUS.md) distinguishes completed research from release
qualification. Machine-readable claim records and a file-hash manifest are in
[corpus/records.jsonl](corpus/records.jsonl) and
[corpus/manifest.json](corpus/manifest.json). The [bibliography](corpus/bibliography.bib)
identifies the sources; their PDFs and transcriptions are not distributed.

## AI assistance

Erik Peterson started and directs the project. Its formalizations, proof
attempts and explanations are model-generated, with separate AI agents
reviewing source/model boundaries and completed proof paths. Lean's kernel
checks proof terms; source faithfulness relies on the documented reviews.
The source-specific guides disclose interpretation and version gaps.

Project material is offered under the [MIT license](LICENSE) for applicable
rights. That license does not cover the source papers or fetched dependencies.
Use [CITATION.cff](CITATION.cff) to cite the collection and cite Peterson and
Fischer separately for their original work. No author-confirmed erratum,
novelty claim or upstream-library acceptance is implied.
