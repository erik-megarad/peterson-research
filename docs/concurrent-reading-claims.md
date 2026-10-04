# Reading an intact value while a writer changes it: exact claims

All declarations below are in namespace `ConcurrentReading`. Links refer to the collection layout. The account's assumptions apply to each claim. Definitions in Targets are obligations, not proof claims.

| Claim | Exact declarations | Module | Meaning and boundary |
| --- | --- | --- | --- |
| integrity | `ConcurrentReading.integrity` | [Integrity](../ConcurrentReading/Integrity.lean) | Every returned sample is untorn and identifies an actually invoked source write; that write may be pending. |
| source-order | `ConcurrentReading.source_order` | [OrderHistory](../ConcurrentReading/OrderHistory.lean) | Completed-write recency, source invocation before response, and no source reversal across nonoverlapping reads on any readers. |
| common-order | `ConcurrentReading.common_ordering` | [Linearization](../ConcurrentReading/Linearization.lean) | One duplicate-free latest-write order for every finite history, respecting real time, with W0 first; may append the pending writer response and omits pending reads. |
| own-work | `ConcurrentReading.own_completion` | [Completion](../ConcurrentReading/Completion.lean) | A pending invocation cannot stay busy through an interval containing 16+6*n successful own abstract actions. |
| eventual-completion | `ConcurrentReading.eventual_own_completion` | [Completion](../ConcurrentReading/Completion.lean) | Unbounded successful own actions imply an idle occurrence; apply to the suffix beginning at a pending invocation. |

The accepted local qualification used the pinned compiler and reused dependency caches. It checked clean root builds, declaration/axiom inventories and locked dependencies. Allowed foundational axioms are `propext`, `Classical.choice` and `Quot.sound`; no project proof placeholders, custom axioms or unsafe proof escape hatches are claimed. This is historical proof evidence, not a fresh build of the assembled collection. Source-faithfulness review and kernel checking are separate.
