# Where a regular-register construction loses atomicity: exact claims

All declarations below are in namespace `MultiReaderAtomic`. Links refer to the collection layout. The account's assumptions apply to each claim. Definitions in Targets are obligations, not proof claims.

| Claim | Exact declarations | Module | Meaning and boundary |
| --- | --- | --- | --- |
| original-refutation | `MultiReaderAtomic.reverseOrder_not_finiteCorrectness`, `MultiReaderAtomic.reverseOrder_not_indexedCriterion`, `MultiReaderAtomic.reverseOrder_not_sourceCriterion` | [Counterexample](../MultiReaderAtomic/Counterexample.lean) | One-reader Nat execution in the original both-orders model violates API and source-lifted BC6. |
| restricted-refutation | `MultiReaderAtomic.regularFc_not_restrictedFiniteCorrectness`, `MultiReaderAtomic.regularFc_not_indexedCriterion`, `MultiReaderAtomic.regularFc_not_sourceCriterion` | [RestrictedCounterexample](../MultiReaderAtomic/RestrictedCounterexample.lean) | Two-reader Nat execution with writer RC-before-FC, all-left-first operands and all calls/primitives completed violates BC6. |
| api-origin | `MultiReaderAtomic.api_provenance_reachable` | [Origin](../MultiReaderAtomic/Origin.lean) | Each API return comes from initialization or a writer already invoked before response; no freshness or atomic ordering follows. |
| completion | `MultiReaderAtomic.ownCompletion`, `MultiReaderAtomic.restrictedOwnCompletion` | [Completion](../MultiReaderAtomic/Completion.lean) | Original and restricted own-operation completion, with writer 3n+5 and reader 2n+8 primitive-call budgets, assuming continued own scheduling and terminating primitives. |
| replay | `MultiReaderAtomic.response_causalReplay` | [CausalTrace](../MultiReaderAtomic/CausalTrace.lean) | A completed response has an actual invocation-rooted instruction replay with sampled operands and supplying witnesses; this is not a cancellation invariant. |

The accepted local qualification used the pinned compiler and reused dependency caches. It checked clean root builds, declaration/axiom inventories and locked dependencies. Allowed foundational axioms are `propext`, `Classical.choice` and `Quot.sound`; no project proof placeholders, custom axioms or unsafe proof escape hatches are claimed. This is historical proof evidence, not a fresh build of the assembled collection. Source-faithfulness review and kernel checking are separate.
