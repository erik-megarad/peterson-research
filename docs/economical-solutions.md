# Economical solutions: small registers, failures and exact guarantees

Peterson and Fischer ask how little shared information processes need to
coordinate a critical section. A small register is attractive, but its size
alone says nothing about whether someone gets stuck. This reconstruction keeps
safety, service, queue order, register economy and timing claims separate.

## Sources and versions

The work is Gary L. Peterson and Michael J. Fischer's *Economical Solutions for
the Critical Section Problem in a Distributed System*, STOC 1977, pp. 91–97.
Both inspected artifacts are extended abstracts: a seven-page proceedings-style
scan and a fourteen-page September 1998 LaTeX restoration. The restoration says
it incorporates a conference erratum, but the separate erratum and complete
paper were unavailable. Page count does not make the restoration a full paper.

| Artifact | SHA-256 |
| --- | --- |
| Proceedings-style scan | `40eee58a3074855a3024e5ea9245167cc4b9ece68f0ff2f9b86b8286e754275a` |
| September 1998 restoration | `0f592d509f44a5eb46063bdeed5cc3f43078f256287b990752b1250124358761` |

Version choice is local to each claim:

| Algorithms | Selected scope |
| --- | --- |
| 1 and 2 | Agreeing operations: restoration pp. 1–6, proceedings pp. 91–93. Algorithm 2's register count selects the proceedings ceiling placement. |
| 3 | Complete proceedings listing, pp. 93–94: complementary upper join and all-upper tick scan. The restoration differs and lacks a tick label. The highest-only prose guard is another variant. |
| 5 | Agreeing outline: restoration pp. 8–10, 13; proceedings pp. 94–96. Separately sampled scans and delayed writes are disclosed expansions. |
| 6 | Proceedings pp. 95–96 with its complete pp. 93–94 clock; agreeing restoration outline pp. 10–11, 13. |
| 7 | Proceedings p. 96 and the complete proceedings clock, compared with restoration pp. 11–13. Both reversed clocks use that interpreter; joint initial publication and scan expansion are reconstruction choices. |

There is no whole-paper equivalence or whole-paper verification assertion.
Results for outline expansions concern those reviewed operational choices,
not every possible implementation of the prose.

## A failure discards the old request

Each process owns one whole visible register. Only its owner ordinarily writes
it; peers read it. Individual reads and writes are atomic, while computations
and cached read results are private. All these operations are interleaved.
The register is the only channel between processes; private memory is not
counted as shared storage.

A failure can occur between operations, even inside the critical section. It
atomically resets the owner's register to dead, removes critical occupancy,
and discards pending work. A failed process may stay down forever. Restart
creates fresh inactive private state; it never resumes a cached write or the
old request. An inactive process need not request again. Thus a dead register
value is not itself proof that the private control is inactive.

This automatic reset/abort model is an assumption of the paper's setting. It
is not crash recovery for a machine that leaves a stale register or keeps
using the resource after being declared failed. Peer failures and restarts
remain unrestricted in the positive results.

Safety and finite-prefix FIFO need no fairness. Positive request service assumes
**instruction-or-own-failure scheduling** and **critical-completion-or-own-failure**:
a pending original request gets its own entry or its own failure; a surviving
request eventually enters. It cannot be satisfied by a later request after
restart. Doorway termination for Algorithms 5/6 needs only the instruction
scheduling premise, allowing an outer critical occupant to remain forever.
The standalone clock has its own active-instruction-or-abort premise.

## What is checked, and why

| Construction | Result and proof idea |
| --- | --- |
| Algorithm 1, two processes | Safety tracks the meaning of the three visible values and the separately sampled reads. Progress follows the pending original request through its two-write protocol; peer failure resets rather than freezes an obstruction. |
| Algorithm 2, every positive population | A padded binary tournament composes two-party contests. Safety derives unique representatives from actual read/write histories and retained lower-level ownership. Progress derives release and advancement, rather than assuming a local contest eventually releases. Complete scan orders, dummy reads and the singleton are covered. |
| Algorithm 5, every positive population | An explicit queue follows the tournament doorway. Historical scan facts support safety; a capacity argument proves doorway completion even without outer critical completion. Progress then serves the full outer request. The enqueue write starts FIFO protection, with both episodes identified and no eventual-entry premise needed for the finite-prefix ordering theorem. |
| Algorithm 6, every positive population | An implicit queue uses the proceedings clock in a constrained client. Historical removal and three-tick completion are derived for this client, supporting doorway completion independently of an outer critical occupant. Actual predecessor episodes yield full request service. Earlier enqueues resolve by their own entry or abort before later entry, including identifier reuse. |
| Algorithm 7, every configured population | The reviewed two-clock reconstruction is safe: derived publication, clock and list histories prevent two actual critical occupants. This safety proof coexists with the failures of progress and a chosen FIFO boundary below. |

These are checked unbounded arguments, not conclusions from finite exploration.
The [exact declaration index](claims.md) names safety, progress, FIFO and doorway
endpoints separately and links directly to their Lean modules.

## Negative results are part of the account

**Proceedings Algorithm 3 need not keep ticking.** A four-position execution has
a 32-step stem and a 21-step complete-state cycle. Three episodes survive and
satisfy the active scheduling premise, but no later tick occurs. The
[Lean witness](../Peterson/EconomicalSolutions/Algorithm3Counterexample.lean)
refutes universal next-outcome and repeated-ticking claims for the selected
listing. A separate restoration two-position experiment is not the theorem
published here. Algorithm 6's positive constrained-client result does not rely
on the refuted unrestricted clock claim.

**Algorithm 7 can reverse strict order at level-two publication.** Two original
episodes yield a bad 206-step prefix, then a 223-step completed prefix with an
admissible idle suffix. The
[checked reversal](../Peterson/EconomicalSolutions/Algorithm7Counterexample.lean)
refutes that exact publication-boundary FIFO target. The source does not fix
that boundary, so it is not a general refutation of every source FIFO reading.

**Algorithm 7 can leave original requests waiting forever.** The
[level-one witness](../Peterson/EconomicalSolutions/Algorithm7LevelOne.lean)
has four processes, a 68-step stem and a 168-step periodic schedule with growing
private counters. It satisfies both frozen liveness premises, yet original
surviving requests have no entry or failure outcome. The checked execution
contradicts whole-request progress and critical-independent doorway termination
for this reconstruction. It is not a complete-state lasso, and the contract
claims the execution and absence of outcomes rather than inventing separately
named universal negation predicates.

## Register economy and initialized solo work

Let h be ceil(log₂ n). These counts concern **one owner's whole visible
register**. Private caches, counters and control state are excluded.

| Algorithm | Checked size |
| --- | --- |
| 1 and 3 | Exact three-value types. |
| 2 | Lossless reachable-register cover of size `1+2*h`. |
| 5 | Cover of size `1+2*h+3*n` for n≥2; two values for n=1. |
| 6 | Cover of size `1+2*h+7` for n≥2; six values for n=1. |
| 7 | Exact fourteen-value type, independent of population. |

A cover gives an upper bound on reachable values; it does not prove that every
covered value is reachable or that the representation is minimal. Each count
has an `ordinary_visible` theorem: holding the actor's complete local state
and all visible registers fixed holds its ordinary instruction result fixed.
Together with nonactor preservation, this connects the count to actual
communication rather than just an unrelated finite datatype.

For the chosen Algorithm 5 representation, a
[checked erasure diagnostic](../Peterson/EconomicalSolutions/Algorithm5Erasure.lean)
shows that discarding all but the specified priority component loses information
needed by the interpreter. It refutes that erasure only, not every possible
smaller implementation.

The [two-state lower bound](../Peterson/EconomicalSolutions/TwoStateBypass.lean)
is universal for a reviewed deterministic owner-register program grammar:
two processes, arbitrary private memory, asymmetric programs and a whole-type
cover with at most two visible values. With failures allowed, reachable safety
and initialized admissible per-request progress cannot both hold. The argument
uses comparison histories and an infinite bypass construction. It is not a
representation theorem for every RAM convention, and its use of failures
matters to the limitation below.

For [Algorithm 2 initialized solo work](../Peterson/EconomicalSolutions/Algorithm2SoloCount.lean),
the actual interpreter reaches its first entry in exactly
`3*2^h+7*h-1 ≤ 13*n` instructions. The proof counts all individual instructions,
including dummy reads, for every positive population and complete order. The
singleton count is two. This measures work from initialization, not elapsed
time or service after an arbitrary previous history.

## Claims that remain unestablished

The following dispositions retain the completed research boundary:

- The source's unspecified existential FIFO point and the weaker interval
  alternative remain unselected, without a general source FIFO verdict. Separate
  level-three completion is unproved and unrefuted; it is unnecessary to refute
  the selected whole-request claim, so no further level-three proof unit is
  scheduled for E5.
- Additive `1+2*h+n` / `1+2*h+5` totals remain unestablished for the general-population reconstructions. The diagnostic refutes only the specified priority-only erasure. Reopen for a concrete code/refinement with actual read/write and admissibility correspondence.
- The separate no-failure assertion after Theorem 3-3: Unestablished, not refuted. The checked construction uses failures; a proof needs a reviewed failure-free return/execution contract and new comparison/reachability argument preserving private history. It is outside the completed lower-bound target.
- For Algorithm 2 solo work: Arbitrary prior histories, other algorithms' solo bounds and host runtime remain unestablished.
- Algorithm 4 delivery, 17 values and 13-value/time tradeoff: Outside selected critical-section proof scope and unestablished. Needs a delivery contract, actual two-clock sender/receiver interpreter and proof. Existing clock counterexamples have no proved A4 transfer.
- Section 5 preliminary parallel bounds, external comparisons and polynomial-clock conjecture: Outside selected proof scope and unestablished. Requires a timed model, charged waiting interval and failure/time-divergence conventions. Preliminary bounds and the conjecture remain source assertions, not checked results or refutations.

CSLib's transition systems, finite paths and infinite executions fit the
relations used here. Message-delivery fairness does not supply register
instruction scheduling or client completion; those predicates and the historical
certificates remain local. No broader library abstraction or upstream submission
is claimed. Read the [verification guide](verification.md) for the distinction
between kernel checks and source-faithfulness review.
