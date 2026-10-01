# Peterson Research

This collection reconstructs selected shared-memory algorithms from Gary L.
Peterson's *The Essential Dekker's Algorithm* and Gary L. Peterson and Michael
J. Fischer's *Economical Solutions for the Critical Section Problem in a
Distributed System*. Lean checks the encoded proofs. The collection includes
successful guarantees and counterexamples: a safe algorithm can still leave
someone waiting forever.

Start with either reading path:

- [Essential Dekker](docs/essential-dekker.md): repeated two-process safety and
  request service, arbitrarily many finite overtakes, the printed generalization's
  obstruction, and safety with starvation after an explicitly selected correction.
- [Economical solutions](docs/economical-solutions.md): Algorithms 1/2 and 5/6
  safety and request service; 5/6 FIFO and doorway termination; clock and
  Algorithm 7 counterexamples; register counts, a failure-model lower bound,
  and initialized solo work.

These are distinct mathematical models. Dekker uses protocol fairness and
critical completion; economical solutions additionally model automatic reset
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

The separate [core Peterson repository](https://github.com/erik-megarad/peterson-algorithm)
contains the completed 1981 algorithm development. This collection does not
change its theorems or publication. The shared Lean root here is a build and
navigation convenience, not an assertion that the papers have the same semantics.

## AI assistance

The formalizations, proof attempts, explanations and publication packet are
model-generated. Erik Peterson started and directed the project and holds
applicable rights; that role does not imply human authorship of every sentence
or independent human mathematical review. Separate AI agents reviewed the
source/model boundaries and completed proof paths. Lean's kernel checks proof
terms, not whether a reconstruction faithfully represents a paper. The
source-specific guides disclose interpretation and version gaps.

Project material is offered under the [MIT license](LICENSE) for applicable
rights. That license does not cover the source papers or fetched dependencies.
Use [CITATION.cff](CITATION.cff) to cite the collection and cite Peterson and
Fischer separately for their original work. No author-confirmed erratum,
novelty claim or upstream-library acceptance is implied.
