# Electing the maximum around a one-way ring: exact claims

All declarations below are in namespace `CircularElection`. Links refer to the collection layout. The account's assumptions apply to each claim. Definitions in Targets are obligations, not proof claims.

| Claim | Exact declarations | Module | Meaning and boundary |
| --- | --- | --- | --- |
| origin | `CircularElection.identifier_origin` | [Origin](../CircularElection/Origin.lean) | Every carried identifier came from an original owner. |
| maximum | `CircularElection.maximum_live`, `CircularElection.live_maximum_exists` | [Maximum](../CircularElection/Maximum.lean) | A maximum identifier remains live before announcement. |
| safety | `CircularElection.election_safety`, `CircularElection.reachable_announcer_maximum` | [Safety](../CircularElection/Safety.lean) | Only the original maximum owner announces. |
| progress | `CircularElection.eventual_election`, `CircularElection.correct_election` | [Progress](../CircularElection/Progress.lean) | Eventual announcement under DeliveryFair and LocalFair. |
| complexity | `CircularElection.message_complexity` | [Complexity](../CircularElection/Complexity.lean) | Actual sends through first announcement are bounded by 3*n*(1+floor(log2 n)), including n=1 and unfair prefixes. |
| traces | `CircularElection.one_process_trace`, `CircularElection.two_process_four_send_trace`, `CircularElection.two_process_five_send_trace` | [Traces](../CircularElection/Traces.lean) | Concrete one- and two-process executions; examples, not exhaustive exploration. |

The accepted local qualification used the pinned compiler and reused dependency caches. It checked clean root builds, declaration/axiom inventories and locked dependencies. Allowed foundational axioms are `propext`, `Classical.choice` and `Quot.sound`; no project proof placeholders, custom axioms or unsafe proof escape hatches are claimed. This is historical proof evidence, not a fresh build of the assembled collection. Source-faithfulness review and kernel checking are separate.
