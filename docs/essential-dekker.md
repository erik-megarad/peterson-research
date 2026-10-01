# Essential Dekker: safety, service and their limits

Mutual exclusion means two processes cannot use a protected resource together.
Request service means a process that asks to enter eventually gets its own
turn. Peterson's compact Dekker variant illustrates why these require separate
arguments: the two-process algorithm has both, but it has no uniform finite
bound on how often a peer can enter first.

## Source and reconstructed operations

The source is Gary L. Peterson's *The Essential Dekker's Algorithm*, June 1986,
revised December 1986. The inspected five-page electronic restoration includes
an October 1994 addendum describing scanning, LaTeX restoration and unspecified
small changes. An independent original 1986 version has not been authenticated.
The retained artifact's SHA-256 is
`27b8e4e14cc31f2913f3f35389c2477bfaabbf35f4d9c01870c90635d2c23d01`.
This is Peterson's account of Dekker, not an original paper by Dekker.

Figure 4 on page 3 is represented in
[TwoProcess.lean](../Peterson/EssentialDekker/TwoProcess.lean).
Each process has an interest flag; a shared turn value breaks ties. Both flags
start false and either initial turn is allowed. A private request begins an
attempt. The process reads turn first and reads the peer flag only if the
first test needs it, keeps the computed value privately, and writes its flag
in a separate step. It then tests its own flag and, when needed, separately
reads the peer flag. An unsuccessful loop repeats this work. After using the
resource, it writes turn to its peer and clears its own flag in separate steps.

This left-to-right short-circuit evaluation is an explicit project interpretation.
The execution is sequentially consistent: all individual shared reads and writes
form one interleaving that respects each process's program order. A computed
value can become stale before its later write. Clearing a flag inside the loop
does not withdraw the private request. Requests after exit are optional, so a
peer may remain inactive forever.

## Why the two-process results fit together

The safety proof maintains a relation between control locations, flags and turn.
It checks every atomic transition, including a delayed write of a cached result.
That invariant rules out simultaneous critical occupancy after any finite
execution; no scheduling fairness is needed. The checked endpoint is
`Peterson.EssentialDekker.TwoProcess.repeated_mutual_exclusion`.

For service, the execution must schedule participating protocol steps weakly
fairly and finish actual critical work eventually. Weak fairness prevents a
continuously active protocol participant from being ignored forever; it does
not demand that a read obtain a favorable value. The proof follows a pending
request through the loop. If it never enters, the peer's behavior and the turn
handoff eventually prevent the assumed endless obstruction. The checked
[request theorem](../Peterson/EssentialDekker/TwoProcessProgressProof.lean)
serves that same request, including when its flag temporarily becomes false.
Idle clients have no duty to make requests.

A finite delay can be arbitrarily long without violating those assumptions.
The [overtaking construction](../Peterson/EssentialDekker/TwoProcessOvertaking.lean)
chooses any natural number k, clears the requester's flag during its loop,
lets the peer complete k passages, and then serves the original request.
An idle suffix gives a valid fair infinite continuation. The existential family
uses requester `false` and initial turn `true`; it does not claim witnesses
for every actor/turn combination. This proves arbitrary finite overtaking,
not starvation, and does not contradict eventual service.

## Figure 6: two different negative statements

Figure 6 on page 5 generalizes the idea using levels and peer counts. The
printed test counts peer flags **less than or equal to** the current level.
At level one, before anyone first passes, every observed flag is zero or one.
Every scan therefore counts all n−1 peers, while passing requires a count
strictly below n−1. Even one active requester with an inactive peer cannot pass.

[LiteralObstruction.lean](../Peterson/EssentialDekker/LiteralObstruction.lean)
checks the scan arithmetic, including the concrete two-process inactive-peer
case. The whole-execution first-level obstruction is a separately reviewed
written argument. It is not presented as a Lean theorem about an infinite
literal interpreter.

The project explicitly selected **greater than or equal to** as a local
correction for a separate model. This is not an authenticated erratum or a
claim that the author approved a repair. In
[Corrected.lean](../Peterson/EssentialDekker/Corrected.lean), ascending scans
read peers one at a time and the process may retreat through levels.

That correction still does not ensure service. The
[starvation witness](../Peterson/EssentialDekker/Starvation.lean) has three
processes, a 96-step stem and a repeating 68-step complete-state cycle.
Every actor keeps running and every critical occupant finishes, yet process
zero's original request never enters. The theorem checks initialization,
every step, fairness, completion and absence of entry for the infinite execution.
It refutes the selected corrected-model progress target without adding a
stronger fairness assumption.

## Corrected arbitrary-n safety remains true

The same corrected model is nevertheless safe for every n at least two,
with repeated requests and arbitrary finite actor schedules. The
[proof](../Peterson/EssentialDekker/CorrectedSafety.lean) follows the final scan:
passing establishes an ordering relation between the process and peers it has
cleared. The invariant preserves the relevant flag and historical ordering
facts across later steps, including retreat and separate reads. Two distinct
critical occupants would violate that relation.

No fairness is needed for this safety result. Safety and the starvation witness
are compatible: the resource is never used by two processes together, while
one requester can be excluded forever. No further repair or positive n-process
progress theorem is included.

The [declaration index](claims.md) and [verification guide](verification.md)
provide exact endpoints and reproduction. Source correspondence and encoded
boundaries passed separate AI semantic review; the source restoration gap
remains. CSLib transition-system abstractions are reused where they fit, while
these control, fairness and history arguments remain source-specific. No
upstream submission is part of this collection.
