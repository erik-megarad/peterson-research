# Exact checked declarations

Each row names the declaration checked by the release contract. Read its source-specific guide for the model and limits. Negative results are proved counterexamples; an unestablished claim is not a theorem.

## essential-dekker

### Figure 4 repeated safety

Two processes never occupy the critical section together, for either initial turn.

- `Peterson.EssentialDekker.TwoProcess.repeated_mutual_exclusion`

[Lean declaration module](../Peterson/EssentialDekker/TwoProcess.lean).

Sequential consistency; individually atomic shared accesses; repeated requests. The selected evaluation order and initialized state are part of the model; no weak-memory or executable-code claim. Two initially false flags; fixed left-to-right short-circuit evaluation; either initial turn. No fairness needed; safety alone gives no service.

### Figure 4 request service

Every private request reaches its matching entry under protocol fairness and critical completion.

- `Peterson.EssentialDekker.TwoProcess.Progress.request_eventually_entry`

[Lean declaration module](../Peterson/EssentialDekker/TwoProcessProgressProof.lean).

Sequential consistency; individually atomic shared accesses; repeated requests. The selected evaluation order and initialized state are part of the model; no weak-memory or executable-code claim. Weak fairness of participating protocol steps and eventual critical completion; idle clients need not request. A loop write clearing a flag does not cancel a request. No elapsed-time or hardware memory-model guarantee.

### Figure 4 arbitrary finite overtaking

For each natural k, a fair execution includes k completed peer passages during one request, then serves that request.

- `Peterson.EssentialDekker.TwoProcess.Overtaking.arbitrary_finite_overtaking`

[Lean declaration module](../Peterson/EssentialDekker/TwoProcessOvertaking.lean).

Sequential consistency; individually atomic shared accesses; repeated requests. The selected evaluation order and initialized state are part of the model; no weak-memory or executable-code claim. Existential witnesses use requester false and initial turn true; the request survives a true-to-false loop flag write. The infinite continuation satisfies the same fairness and critical-completion premises as request service. Not starvation or a universal actor/turn witness claim; no uniform finite overtaking bound.

### Printed Figure 6 arithmetic obstruction

When all first-level observations are at most one, the printed count test cannot pass.

- `Peterson.EssentialDekker.LiteralObstruction.count_all`
- `Peterson.EssentialDekker.LiteralObstruction.first_level_test_false`
- `Peterson.EssentialDekker.LiteralObstruction.inactive_peer_test_false`

[Lean declaration module](../Peterson/EssentialDekker/LiteralObstruction.lean).

Printed comparison is less-than-or-equal; n at least two; scans omit self. The full source-literal execution obstruction is a reviewed written argument, not a Lean execution theorem.

### Corrected Figure 6 starvation

An initialized three-process infinite execution schedules every actor and completes critical work, but one request never enters.

- `Peterson.EssentialDekker.Corrected.Starvation.corrected_progress_counterexample`

[Lean declaration module](../Peterson/EssentialDekker/Starvation.lean).

Sequential consistency; individually atomic shared accesses; repeated requests. The selected evaluation order and initialized state are part of the model; no weak-memory or executable-code claim. Explicit local correction replaces the count comparison by greater-than-or-equal; not an authenticated erratum. Three processes; individually sampled ascending scans; unchanged protocol fairness and critical completion. Negative progress result; no positive arbitrary-n service or further repair claimed.

### Corrected Figure 6 arbitrary-n safety

For every n at least two, repeated use preserves mutual exclusion under arbitrary finite actor schedules.

- `Peterson.EssentialDekker.Corrected.Safety.mutual_exclusion`
- `Peterson.EssentialDekker.Corrected.Safety.run_mutual_exclusion`

[Lean declaration module](../Peterson/EssentialDekker/CorrectedSafety.lean).

Sequential consistency; individually atomic shared accesses; repeated requests. The selected evaluation order and initialized state are part of the model; no weak-memory or executable-code claim. The same corrected comparison, ascending separate scans and level retreat as the starvation model. No fairness needed; safety does not repair refuted progress.

## economical-solutions

### Algorithm 1 safety

Algorithm 1 preserves mutual exclusion in every initialized execution of its reviewed interpreter.

- `EconomicalSolutions.Algorithm1.mutual_exclusion`
- `EconomicalSolutions.Algorithm1.finite_execution_mutual_exclusion`

[Lean declaration module](../Peterson/EconomicalSolutions/Algorithm1Safety.lean).

Individually atomic process-owned whole registers; private caches; automatic reset to dead and abort on failure; optional fresh inactive restart. Original requests remain distinct across failures and identifier reuse; repeated requests and unrestricted peer failures are allowed. Two processes. No elapsed-time or hardware memory-model guarantee. No fairness needed.

### Algorithm 2 safety

Algorithm 2 preserves mutual exclusion in every initialized execution of its reviewed interpreter.

- `EconomicalSolutions.Algorithm2.safety`

[Lean declaration module](../Peterson/EconomicalSolutions/Algorithm2Refinement.lean).

Individually atomic process-owned whole registers; private caches; automatic reset to dead and abort on failure; optional fresh inactive restart. Original requests remain distinct across failures and identifier reuse; repeated requests and unrestricted peer failures are allowed. Every positive population and the complete scan orders required by the configuration; dummy positions and singleton included. No elapsed-time or hardware memory-model guarantee. No fairness needed.

### Algorithm 5 safety

Algorithm 5 preserves mutual exclusion in every initialized execution of its reviewed interpreter.

- `EconomicalSolutions.Algorithm5.safety`

[Lean declaration module](../Peterson/EconomicalSolutions/Algorithm5Invariant.lean).

Individually atomic process-owned whole registers; private caches; automatic reset to dead and abort on failure; optional fresh inactive restart. Original requests remain distinct across failures and identifier reuse; repeated requests and unrestricted peer failures are allowed. Every positive population and the complete scan orders required by the configuration; dummy positions and singleton included. Source outline expanded into separate scans and delayed writes. No elapsed-time or hardware memory-model guarantee. No fairness needed.

### Algorithm 6 safety

Algorithm 6 preserves mutual exclusion in every initialized execution of its reviewed interpreter.

- `EconomicalSolutions.Algorithm6.safety`

[Lean declaration module](../Peterson/EconomicalSolutions/Algorithm6Invariant.lean).

Individually atomic process-owned whole registers; private caches; automatic reset to dead and abort on failure; optional fresh inactive restart. Original requests remain distinct across failures and identifier reuse; repeated requests and unrestricted peer failures are allowed. Every positive population and the complete scan orders required by the configuration; dummy positions and singleton included. Source outline expanded into separate scans and delayed writes. No elapsed-time or hardware memory-model guarantee. No fairness needed.

### Algorithm 7 safety

Algorithm 7 preserves mutual exclusion in every initialized execution of its reviewed interpreter.

- `EconomicalSolutions.Algorithm7.PrepublicationHistory.mutual_exclusion`
- `EconomicalSolutions.Algorithm7.PrepublicationHistory.run_mutual_exclusion`

[Lean declaration module](../Peterson/EconomicalSolutions/Algorithm7Prepublication.lean).

Individually atomic process-owned whole registers; private caches; automatic reset to dead and abort on failure; optional fresh inactive restart. Original requests remain distinct across failures and identifier reuse; repeated requests and unrestricted peer failures are allowed. Every positive population and the complete scan orders required by the configuration; dummy positions and singleton included. Source outline expanded into separate scans and delayed writes. No elapsed-time or hardware memory-model guarantee. No fairness needed.

### Algorithm 1 original-request progress

A pending request reaches its own entry or failure; a surviving original request enters.

- `EconomicalSolutions.Algorithm1.pending_first_outcome`
- `EconomicalSolutions.Algorithm1.per_request_progress`
- `EconomicalSolutions.Algorithm1.deadlock_freedom`

[Lean declaration module](../Peterson/EconomicalSolutions/Algorithm1Progress.lean).

Individually atomic process-owned whole registers; private caches; automatic reset to dead and abort on failure; optional fresh inactive restart. Original requests remain distinct across failures and identifier reuse; repeated requests and unrestricted peer failures are allowed. Instruction-or-own-failure scheduling and critical-completion-or-own-failure; service applies to the original surviving request. Two processes for A1; every positive population and complete configured scan orders for A2/A5/A6. No elapsed-time or hardware memory-model guarantee.

### Algorithm 2 original-request progress

A pending request reaches its own entry or failure; a surviving original request enters.

- `EconomicalSolutions.Algorithm2.pending_first_outcome`
- `EconomicalSolutions.Algorithm2.per_request_progress`
- `EconomicalSolutions.Algorithm2.deadlock_freedom`

[Lean declaration module](../Peterson/EconomicalSolutions/Algorithm2Progress.lean).

Individually atomic process-owned whole registers; private caches; automatic reset to dead and abort on failure; optional fresh inactive restart. Original requests remain distinct across failures and identifier reuse; repeated requests and unrestricted peer failures are allowed. Instruction-or-own-failure scheduling and critical-completion-or-own-failure; service applies to the original surviving request. Two processes for A1; every positive population and complete configured scan orders for A2/A5/A6. No elapsed-time or hardware memory-model guarantee.

### Algorithm 5 original-request progress

A pending request reaches its own entry or failure; a surviving original request enters.

- `EconomicalSolutions.Algorithm5.pending_first_outcome`
- `EconomicalSolutions.Algorithm5.surviving_request_enters`
- `EconomicalSolutions.Algorithm5.deadlock_freedom`

[Lean declaration module](../Peterson/EconomicalSolutions/Algorithm5Progress.lean).

Individually atomic process-owned whole registers; private caches; automatic reset to dead and abort on failure; optional fresh inactive restart. Original requests remain distinct across failures and identifier reuse; repeated requests and unrestricted peer failures are allowed. Instruction-or-own-failure scheduling and critical-completion-or-own-failure; service applies to the original surviving request. Two processes for A1; every positive population and complete configured scan orders for A2/A5/A6. No elapsed-time or hardware memory-model guarantee.

### Algorithm 6 original-request progress

A pending request reaches its own entry or failure; a surviving original request enters.

- `EconomicalSolutions.Algorithm6.pending_first_outcome`
- `EconomicalSolutions.Algorithm6.pending_surviving_enters`
- `EconomicalSolutions.Algorithm6.surviving_pending_deadlock_freedom`

[Lean declaration module](../Peterson/EconomicalSolutions/Algorithm6Predecessor.lean).

Individually atomic process-owned whole registers; private caches; automatic reset to dead and abort on failure; optional fresh inactive restart. Original requests remain distinct across failures and identifier reuse; repeated requests and unrestricted peer failures are allowed. Instruction-or-own-failure scheduling and critical-completion-or-own-failure; service applies to the original surviving request. Two processes for A1; every positive population and complete configured scan orders for A2/A5/A6. No elapsed-time or hardware memory-model guarantee.

### Proceedings Algorithm 3 ticking refuted

A four-position fair infinite execution has three surviving episodes with no later tick.

- `EconomicalSolutions.Algorithm3.Counterexample.fair_non_ticking_lasso`
- `EconomicalSolutions.Algorithm3.Counterexample.not_universal_next_outcome`
- `EconomicalSolutions.Algorithm3.Counterexample.not_universal_repeated_ticks`

[Lean declaration module](../Peterson/EconomicalSolutions/Algorithm3Counterexample.lean).

Individually atomic process-owned whole registers; private caches; automatic reset to dead and abort on failure; optional fresh inactive restart. Original requests remain distinct across failures and identifier reuse; repeated requests and unrestricted peer failures are allowed. Complete proceedings clock: complementary upper join and all-upper tick scan; active instruction-or-abort premise. 32-step stem and 21-step complete-state cycle. Not the different restoration guard, highest-only prose guard, or an Algorithm 4 refutation.

### Algorithm 5 FIFO

The enqueue write starts FIFO protection, with both original episodes identified.

- `EconomicalSolutions.Algorithm5.finite_prefix_fifo`
- `EconomicalSolutions.Algorithm5.fifo_entry_order`

[Lean declaration module](../Peterson/EconomicalSolutions/Algorithm5FIFO.lean).

Individually atomic process-owned whole registers; private caches; automatic reset to dead and abort on failure; optional fresh inactive restart. Original requests remain distinct across failures and identifier reuse; repeated requests and unrestricted peer failures are allowed. Finite-prefix claim; enqueue boundary; both original episodes identified. No fairness or eventual-entry premise; FIFO does not by itself establish progress.

### Algorithm 6 FIFO

An earlier enqueue resolves by its own entry or abort before a later episode enters, even with identifier reuse.

- `EconomicalSolutions.Algorithm6.finite_prefix_fifo_original_episode`

[Lean declaration module](../Peterson/EconomicalSolutions/Algorithm6History.lean).

Individually atomic process-owned whole registers; private caches; automatic reset to dead and abort on failure; optional fresh inactive restart. Original requests remain distinct across failures and identifier reuse; repeated requests and unrestricted peer failures are allowed. Finite-prefix claim; enqueue boundary; both original episodes identified. No fairness or eventual-entry premise; FIFO does not by itself establish progress.

### Algorithm 5 critical-independent doorway

A surviving original request reaches its first enqueue even if an outer critical occupant never finishes.

- `EconomicalSolutions.Algorithm5.doorway_first_outcome`
- `EconomicalSolutions.Algorithm5.doorway_surviving_enqueues`

[Lean declaration module](../Peterson/EconomicalSolutions/Algorithm5Doorway.lean).

Individually atomic process-owned whole registers; private caches; automatic reset to dead and abort on failure; optional fresh inactive restart. Original requests remain distinct across failures and identifier reuse; repeated requests and unrestricted peer failures are allowed. Instruction-or-own-failure scheduling only; no outer critical-completion premise. This terminates the doorway, not the whole request. A6 constrained-client ticking is proved separately; it does not assume the refuted unrestricted A3 theorem.

### Algorithm 6 critical-independent doorway

A surviving original request reaches its first enqueue even if an outer critical occupant never finishes.

- `EconomicalSolutions.Algorithm6.doorway_first_outcome`
- `EconomicalSolutions.Algorithm6.doorway_surviving_enqueues`

[Lean declaration module](../Peterson/EconomicalSolutions/Algorithm6Doorway.lean).

Individually atomic process-owned whole registers; private caches; automatic reset to dead and abort on failure; optional fresh inactive restart. Original requests remain distinct across failures and identifier reuse; repeated requests and unrestricted peer failures are allowed. Instruction-or-own-failure scheduling only; no outer critical-completion premise. This terminates the doorway, not the whole request. A6 constrained-client ticking is proved separately; it does not assume the refuted unrestricted A3 theorem.

### Algorithm 7 publication FIFO refuted

A later level-two publication enters before an earlier original episode.

- `EconomicalSolutions.Algorithm7.Counterexample.publication_reversal`
- `EconomicalSolutions.Algorithm7.Counterexample.not_universal_publication_fifo`

[Lean declaration module](../Peterson/EconomicalSolutions/Algorithm7Counterexample.lean).

Individually atomic process-owned whole registers; private caches; automatic reset to dead and abort on failure; optional fresh inactive restart. Original requests remain distinct across failures and identifier reuse; repeated requests and unrestricted peer failures are allowed. Reviewed proceedings-clock reconstruction; two original episodes; 206-step bad prefix and 223-step completed prefix with admissible idle suffix. Not a general source FIFO refutation: the source leaves its FIFO point unspecified.

### Algorithm 7 original-request starvation

A four-process execution meets both frozen liveness premises while original surviving requests have no entry or failure outcome.

- `EconomicalSolutions.Algorithm7.LevelOneCounterexample.level_one_starvation`
- `EconomicalSolutions.Algorithm7.LevelOneCounterexample.not_level_one_completion_or_failure`
- `EconomicalSolutions.Algorithm7.LevelOneCounterexample.original_requests`
- `EconomicalSolutions.Algorithm7.LevelOneCounterexample.no_original_outcomes`

[Lean declaration module](../Peterson/EconomicalSolutions/Algorithm7LevelOne.lean).

Individually atomic process-owned whole registers; private caches; automatic reset to dead and abort on failure; optional fresh inactive restart. Original requests remain distinct across failures and identifier reuse; repeated requests and unrestricted peer failures are allowed. Instruction-or-own-failure scheduling and critical-completion-or-own-failure; service applies to the original surviving request. Reviewed outline expansion with joint initial publication and two reversed proceedings clocks; 68-step stem, 168-step period, growing private counters. The execution contradicts whole-request progress and doorway conclusions for this reconstruction; no separately named universal negation is claimed. Separate level-three completion is unproved and unrefuted.

### Algorithm 1 register economy and communication

Exactly three values in one owner register. Ordinary instructions depend only on the actor local state and visible registers.

- `EconomicalSolutions.Algorithm1.value_card`
- `EconomicalSolutions.Algorithm1.ordinary_visible`

[Lean declaration module](../Peterson/EconomicalSolutions/Algorithm13Economy.lean).

Individually atomic process-owned whole registers; private caches; automatic reset to dead and abort on failure; optional fresh inactive restart. Original requests remain distinct across failures and identifier reuse; repeated requests and unrestricted peer failures are allowed. Counts measure one whole owner register, excluding private memory. A2 selects the proceedings ceiling placement. Cover sizes are upper bounds, not minimality or all-values-reachable claims. No progress or timing follows from a register count.

### Algorithm 3 register economy and communication

Exactly three values for the complete proceedings clock register. Ordinary instructions depend only on the actor local state and visible registers.

- `EconomicalSolutions.Algorithm3.value_card`
- `EconomicalSolutions.Algorithm3.ordinary_visible`

[Lean declaration module](../Peterson/EconomicalSolutions/Algorithm13Economy.lean).

Individually atomic process-owned whole registers; private caches; automatic reset to dead and abort on failure; optional fresh inactive restart. Original requests remain distinct across failures and identifier reuse; repeated requests and unrestricted peer failures are allowed. Counts measure one whole owner register, excluding private memory. A2 selects the proceedings ceiling placement. Cover sizes are upper bounds, not minimality or all-values-reachable claims. No progress or timing follows from a register count.

### Algorithm 2 register economy and communication

A lossless reachable-register cover of size 1+2*h, h=ceil(log2 n). Ordinary instructions depend only on the actor local state and visible registers.

- `EconomicalSolutions.Algorithm2.alphabet_card`
- `EconomicalSolutions.Algorithm2.reachable_register`
- `EconomicalSolutions.Algorithm2.ordinary_visible`

[Lean declaration module](../Peterson/EconomicalSolutions/Algorithm2Economy.lean).

Individually atomic process-owned whole registers; private caches; automatic reset to dead and abort on failure; optional fresh inactive restart. Original requests remain distinct across failures and identifier reuse; repeated requests and unrestricted peer failures are allowed. Counts measure one whole owner register, excluding private memory. A2 selects the proceedings ceiling placement. Cover sizes are upper bounds, not minimality or all-values-reachable claims. No progress or timing follows from a register count.

### Algorithm 5 register economy and communication

A reachable-register cover of size 1+2*h+3*n for n>=2; two for n=1. Ordinary instructions depend only on the actor local state and visible registers.

- `EconomicalSolutions.Algorithm5.alphabet_card_ge_two`
- `EconomicalSolutions.Algorithm5.alphabet_card_singleton`
- `EconomicalSolutions.Algorithm5.reachable_register`
- `EconomicalSolutions.Algorithm5.ordinary_visible`

[Lean declaration module](../Peterson/EconomicalSolutions/Algorithm5Economy.lean).

Individually atomic process-owned whole registers; private caches; automatic reset to dead and abort on failure; optional fresh inactive restart. Original requests remain distinct across failures and identifier reuse; repeated requests and unrestricted peer failures are allowed. Counts measure one whole owner register, excluding private memory. A2 selects the proceedings ceiling placement. Cover sizes are upper bounds, not minimality or all-values-reachable claims. No progress or timing follows from a register count.

### Algorithm 6 register economy and communication

A reachable-register cover of size 1+2*h+7 for n>=2; six for n=1. Ordinary instructions depend only on the actor local state and visible registers.

- `EconomicalSolutions.Algorithm6.alphabet_card_ge_two`
- `EconomicalSolutions.Algorithm6.alphabet_card_singleton`
- `EconomicalSolutions.Algorithm6.reachable_register`
- `EconomicalSolutions.Algorithm6.ordinary_visible`

[Lean declaration module](../Peterson/EconomicalSolutions/Algorithm6Economy.lean).

Individually atomic process-owned whole registers; private caches; automatic reset to dead and abort on failure; optional fresh inactive restart. Original requests remain distinct across failures and identifier reuse; repeated requests and unrestricted peer failures are allowed. Counts measure one whole owner register, excluding private memory. A2 selects the proceedings ceiling placement. Cover sizes are upper bounds, not minimality or all-values-reachable claims. No progress or timing follows from a register count.

### Algorithm 7 register economy and communication

Exactly fourteen visible-register values, independent of population. Ordinary instructions depend only on the actor local state and visible registers.

- `EconomicalSolutions.Algorithm7.value_card`
- `EconomicalSolutions.Algorithm7.ordinary_visible`

[Lean declaration module](../Peterson/EconomicalSolutions/Algorithm7Economy.lean).

Individually atomic process-owned whole registers; private caches; automatic reset to dead and abort on failure; optional fresh inactive restart. Original requests remain distinct across failures and identifier reuse; repeated requests and unrestricted peer failures are allowed. Counts measure one whole owner register, excluding private memory. A2 selects the proceedings ceiling placement. Cover sizes are upper bounds, not minimality or all-values-reachable claims. No progress or timing follows from a register count.

### Algorithm 5 priority-only erasure fails

The specified priority-only erasure cannot factor the actual instruction behavior.

- `EconomicalSolutions.Algorithm5.erasure_witness`
- `EconomicalSolutions.Algorithm5.erasure_does_not_factor`

[Lean declaration module](../Peterson/EconomicalSolutions/Algorithm5Erasure.lean).

Individually atomic process-owned whole registers; private caches; automatic reset to dead and abort on failure; optional fresh inactive restart. Original requests remain distinct across failures and identifier reuse; repeated requests and unrestricted peer failures are allowed. Only this specified erasure is refuted; additive A5/A6 totals remain unestablished.

### Failure-model two-state impossibility

Reachable safety and initialized admissible per-request progress cannot both hold for the reviewed deterministic owner-register grammar with at most two values.

- `EconomicalSolutions.TwoState.Program.binary_impossibility`

[Lean declaration module](../Peterson/EconomicalSolutions/TwoStateBypass.lean).

Two processes; deterministic owner-register programs; arbitrary private memory and asymmetric programs; whole-type at-most-two-value cover. Failures and automatic resets are allowed; the witness uses them. No representation theorem for every RAM convention. The separate failure-free strengthening is unestablished, not refuted.

### Algorithm 2 initialized solo first-entry work

The first entry takes exactly 3*2^h+7*h-1 interpreter instructions, at most 13*n, for h=ceil(log2 n).

- `EconomicalSolutions.Algorithm2.Solo.initialized_first_entry`
- `EconomicalSolutions.Algorithm2.Solo.initialized_lts`
- `EconomicalSolutions.Algorithm2.Solo.count_linear`

[Lean declaration module](../Peterson/EconomicalSolutions/Algorithm2SoloCount.lean).

Initialized solo execution; every positive population and complete scan order; includes dummy reads and singleton count two. Arbitrary prior histories, other algorithms solo bounds and host runtime remain unestablished.

## Round-two papers

Each source-specific map lists exact modules and declarations, scope and assumptions:

- [Circular election](circular-election-claims.md)
- [Concurrent reading](concurrent-reading-claims.md)
- [Multi-reader atomic values](multi-reader-atomic-claims.md)

The shared `publication-checks.toml` and corpus records include these 16 claim records alongside the original 31. Atomicity refutations and own-completion guarantees remain separate claims.
