# Why constant-depth decisions don't work

**Status: negative result, fully self-contained.** This document records why a *fixed*
decision depth cannot replace the graph-dependent `MaxDepth` bound in HPaxos, and gives
the counterexamples in enough detail to rebuild them from scratch. It depends on no
files outside itself.

`main`'s rule — decisions at depth `MaxDepth(alpha)`, proven safe and live — is
**unaffected**. The experiment described here tried to simplify that away and failed;
the way it failed is evidence that `MaxDepth` is the *tight* bound, not merely a
sufficient one.

---

## 1. What was tried

Replace the `MaxDepth(alpha)`-deep decision rule with a constant, `3`:

```
DecisionSlow(m, alpha, b) ==
  SigS({x \in TranClosure(m) : B(x) = b /\ HasDepth(alpha, x, 3, Caught(x))})
    \in Quorums(alpha)
```

together with a *caught-set-parameterised*, *self-judged* freshness stack. Written out,
the definitions under test were:

```
Caught(m)              == CaughtS(Tran(m))        \* acceptors with two Tran-incomparable
                                                  \* messages inside m's history
ConFromCaught(a, c)    == {b \in Learners : \E s \in SafetySets({a,b}) : s \cap c = {}}
IsOneB(m)              == ~IsProposal(m) /\ Cardinality({x \in Tran(m) : B(x)=B(m)}) = 2

Fresh(alpha, m, c) ==
  \A x \in Tran(m) :
    \/ V(x) = V(m)                                                       \* (a) agrees
    \/ ConFromCaught(alpha,c) \cap Lrns(x, Caught(x)) = {}                \* (b) unattested
    \/ \E p \in TranExclusive(m) :                                        \* (c) excused
         B(p) > B(x) /\ ConFromCaught(alpha,c) \cap Lrns(p, Caught(p)) # {}

FreshI(alpha, m, c)    == \A cc : Caught(m) \subseteq cc /\ cc \subseteq c
                                  => Fresh(alpha, m, cc)
Qd(alpha, m, d, c)     == {x \in TranExclusive(m) : d > 0 /\ B(x) = B(m)
                                                   /\ HasDepth(alpha, x, d-1, c)}
HasDepth(alpha, m, d, c) ==
  /\ Sig(m) \in Acceptors
  /\ IF d = 0 THEN IsOneB(m) /\ FreshI(alpha, m, c)
              ELSE SigS(Qd(alpha, m, d, c)) \in Quorums(alpha)
Lrns(m, c)             == {alpha \in Learners : HasDepth(alpha, m, 1, c)}
```

Throughout, **(a)/(b)/(c)** name the three disjuncts of `Fresh`. Two features matter:

- **self-judged attestation** — clauses (b) and (c) consult `Lrns(x, Caught(x))`, each
  message's attesters computed at *its own* caught set. This was adopted deliberately: it
  closes a laundering hole in which an attacker borrows an attestation computed at a
  conveniently small caught set.
- **interval freshness** — `FreshI` requires freshness at *every* caught set between the
  message's own and the judging one. Adopted to close a separate hole (a message
  inflating its own view with incomparable junk to trivialise its tower's obligations).

Both are strictly stronger than the naive alternatives. The counterexample below defeats
the rule anyway, in both interval and pointwise freshness.

## 2. Vocabulary

Non-standard terms used here, defined once (none are repo or paper terms):

| term | meaning |
|---|---|
| **round** | one message per acceptor of a quorum, each referencing all of the previous round. Rounds build depth: a 1b is depth 0, a 2a over a quorum of depth-0 messages is depth 1, etc. |
| **W** | the set in `DecisionSlow`: the depth-3 messages at the decided ballot whose signers form a quorum |
| **tower** | a depth-*d* message together with the messages witnessing its depth (`Qd`, then their `Qd`s, down to the 1bs) |
| **carrier** | the learner a tower's top message attests, i.e. `lambda \in Lrns(top, Caught(top))` |
| **witness** | the acceptor shared between two quorums (exists by `ValidLearnerGraphAssumption`) |
| **pivot** | the honest acceptor, whose 1b necessarily carries its entire history |
| **payload** | a message inside a view that survives clauses (a) and (b), so (c) must fire |
| **excuse** | the `p` supplied by clause (c) |
| **view** | the caught-set parameter `c` at which a judgment is made; "its own view" means `c = Caught(m)` |
| **partial chain** | an acceptor referencing one of its own earlier messages but *not* its latest — the key adversarial move |

## 3. The test graph (K5), stated completely

Machine-checked to satisfy every `LearnerGraphAssumption`.

- **Acceptors** `1..11`: the ten edges of the complete graph on `{1..5}`, indexed
  `(1,2)=1, (1,3)=2, (1,4)=3, (1,5)=4, (2,3)=5, (2,4)=6, (2,5)=7, (3,4)=8, (3,5)=9,
  (4,5)=10`, plus a private acceptor `11`.
- **Learners** `1..5`: the vertices.
- **Minimal quorums** `Q(v)` = the four edges at `v`, plus `{11}` when `v = 5`:

  | learner | 1 | 2 | 3 | 4 | 5 |
  |---|---|---|---|---|---|
  | `Q` | {1,2,3,4} | {1,5,6,7} | {2,5,8,9} | {3,6,8,10} | {4,7,9,10,11} |

  Any two meet in exactly one acceptor, and no three share one.
- **Safety-set generators**: `gen(m) = Acceptors \ UNION {Q(w) : w < m}`, and the
  generator of the pair `{x,y}` is `gen(min(x,y))`:

  | learner | 1 | 2 | 3 | 4 | 5 |
  |---|---|---|---|---|---|
  | `gen` | {1..11} | {5..11} | {8,9,10,11} | {10,11} | {11} |

  So `ConFromCaught(a,c) = {b : (gen(a) \cup gen(b)) \cap c = {}}`.
- `MaxDepth(5) = 5`. **Honest = {11}** only; acceptors `1..10` are Byzantine, so every
  non-`5` learner's quorum is fully forgeable.
- `BalToVal`: ballot 0 has value 0, every higher ballot value 1.

## 4. The counterexample: nested partial chains

`alpha = beta = 5`. Message ids `0..59`; `priors` is the reference set.

**The value-0 decision (ballot 0), four rounds by `Q(5) = {4,7,9,10,11}`:**

| ids | sender per id | priors | meaning |
|---|---|---|---|
| 0 | — | {} | proposal, ballot 0 |
| 1–5 | 4,7,9,10,11 | {0} | round 1 (1bs), depth 0 |
| 6–10 | 4,7,9,10,11 | {1..5} | round 2, depth 1 |
| 11–15 | 4,7,9,10,11 | {6..10} | round 3, depth 2 |
| 16–20 | 4,7,9,10,11 | {11..15} | round 4, depth 3 — this is **W** |

So acceptor 4's messages are 1, 6, 11, 16; acceptor 7's are 2, 7, 12, 17; acceptor 9's
are 3, 8, 13, 18; acceptor 10's are 4, 9, 14, 19; acceptor 11's are 5, 10, 15, 20.
`alpha = 5` decides value 0 at ballot 0.

**Three nested excuse towers.** Each is a depth-1 tower on a different learner's quorum,
and in each, one witness *partial-chains*:

| ballot | carrier | quorum | ids | priors | note |
|---|---|---|---|---|---|
| 1 | learner 1 | {1,2,3,4} | 21 | {} | proposal |
| | | | 22 (by 4) | {21, **1**} | partial chain at round 1 |
| | | | 23,24,25 (by 1,2,3) | {21} | |
| | | | 26 (by 1) | {22,23,24,25} | tower top, attests learner 1 |
| 2 | learner 2 | {1,5,6,7} | 27 | {} | proposal |
| | | | 28 (by 7) | {27, **7**, 26} | partial chain at round 2; links ballot-1 tower |
| | | | 29 (by 1) | {27, 26} | |
| | | | 30,31 (by 5,6) | {27} | |
| | | | 32 (by 5) | {28,29,30,31} | tower top, attests learner 2 |
| 3 | learner 3 | {2,5,8,9} | 33 | {} | proposal |
| | | | 34 (by 9) | {33, **13**, 32} | partial chain at round 3; links ballot-2 tower |
| | | | 35,36,37 (by 2,5,8) | {33, 32} | |
| | | | 38 (by 2) | {34,35,36,37} | tower top, attests learner 3 |

**The value-1 decision (ballot 4), by learner 5:**

| ids | sender | priors | note |
|---|---|---|---|
| 39 | — | {} | proposal, ballot 4 |
| 40 | 11 | {39, **20**, 38} | the honest pivot: full chain + ballot-3 tower |
| 41 | 10 | {39, 14, 38} | partial chain at round 3 |
| 42,43,44 | 9,7,4 | {39, 38} | their earlier messages arrive via the tower |
| 45–49 | 4,7,9,10,11 | {40..44} | round 2 |
| 50–54 | 4,7,9,10,11 | {45..49} | round 3 |
| 55–59 | 4,7,9,10,11 | {50..54} | round 4 — depth 3 |

**Verdicts** (mirror and TLC agree, in *both* pointwise and interval freshness):

```
Caught(22) = {}      Caught(28) = {}      Caught(34) = {4}     Caught(40) = {4,7}
Lrns(26,·) = {1}     Lrns(32,·) = {2}     Lrns(38,·) = {3}
low decision  (value 0 @ ballot 0, learner 5): TRUE
high decision (value 1 @ ballot 4, learner 5): TRUE
c* = CaughtS(closure) = {4,7,9,10};   5 \in ConFromCaught(5, c*): TRUE
```

Two connected learners (here the same learner) decide different values. **Agreement is
violated.**

### Why it works

The honest acceptor 11 must reference its own last message, round-4 message 20, so its
ballot-4 1b drags the entire value-0 structure into view. Every value-0 message there is
payload, and clause (c) needs an excuse. The towers supply it, and the *partial chain* is
what makes them cheap:

1. **The equivocation is never co-visible.** When acceptor 9 references its round-3
   message 13 but not its round-4 message 18, it has equivocated — 18 and 34 are
   incomparable. But round-4 messages are the top of the structure: *nothing references
   them*. So no view in the DAG contains both halves, and 9 is caught only in the global
   closure, where it is harmless (`9 \notin gen(5)`). Every earlier attack died because
   the catch surfaced in a view where an excuse was being consumed; this one never does.
2. **The obligation thins.** Chaining only to round *k* leaves a depth-(*k*−1) payload —
   strictly smaller than the obligation the tower discharges. Ballot 3 handles a depth-3
   obligation while incurring a depth-2 one; ballot 2 incurs depth 1; ballot 1 incurs
   depth 0. Depth-0 payload is bare 1bs, which no learner attests (there is no quorum
   beneath a 1b), so clause (b) dismisses them for free. **The regress terminates
   legitimately.**
3. **Descending carriers absorb the residue.** The pivot's full chain does expose
   acceptors 4 and 7 (their tower 1bs skip round-2/3 messages that message 20 drags in),
   so `Caught(40) = {4,7}`, which disconnects learners 1 and 2. Ordering the carriers
   3 > 2 > 1 puts those two only in the *inner* views, where the catches don't exist;
   the outer view needs only learner 3, and `gen(3) = {8,9,10,11}` misses `{4,7}`.

### Why the earlier attacks failed and this one doesn't

Four previous constructions (a laundering probe, a four-round staircase, a
non-monotonicity attack, an honest-gate attack) all had each acceptor either *fully
chain* or *fully dodge*. Fully dodge and the fork becomes visible in a consuming view, or
the pair disconnects and the agreement claim lapses. Fully chain and the payload never
thins, so the excuse regress never terminates. Partial chaining gets both at once.

### Verification status

Machine-confirmed by TLC in both freshness modes: all 14 probes matched, high decision
`TRUE`, ~2.4 h (pointwise) and ~2.7 h (interval). One practical lesson worth carrying:
TLC does **not** memoise `RECURSIVE` operators, so a transitive-closure operator over a
60-message DAG is re-evaluated along every path (37,831 calls at the top message) and the
direct encoding takes ~17 h. Supplying the closure as an explicit table cuts it to ~2.5 h.
Since TLAPS cannot process `RECURSIVE` at all, soundness of that substitution has to be
established as *table satisfies the recurrence* + *the recurrence has a unique solution*
— which is a generally useful shape for model-checking recursive definitions.

## 5. The repair attempts, and the counterexample that kills each

Writing **U** for "judge attesters at the judging view `c`", i.e. replace
`Lrns(x, Caught(x))` by `Lrns(x, c)` in `Fresh`:

| repair | nested CE §4 | `beta=4` §5.2 | disconnect-then-decide §5.3 | liveness |
|---|---|---|---|---|
| committed defs (self-judged) | **VIOLATION** | **VIOLATION** | holds | ok |
| **(b′)** excuses contain what they excuse | — | — | — | deadlocks with **no failures at all** |
| **R3** `Qd` drops signers caught in `c` | blocked | **VIOLATION** | holds | ok, but disattests decisions |
| **U**, both clauses | blocked | blocked | **VIOLATION** | STALL |
| **U** in clause (b) only (payload) | **VIOLATION** | **VIOLATION** | **VIOLATION** | ok |
| **U** in clause (c) only (excuse) | blocked | blocked | holds | STALL |

Read the last three rows together: re-judging the **excuse** clause is the entire
protection against nesting *and* the entire liveness cost, while re-judging the
**payload** clause buys nothing and introduces a second, independent agreement violation.
No setting of the two switches is both safe and live.

### 5.1 — (b′): two mutually unaware messages deadlock the protocol

No Byzantine behaviour required. Let two depth-1 messages exist at different ballots and
different values, neither referencing the other, and let both become known to everyone. A
new 1b sees both and must dispose of the lower-valued one; under (b′) the only admissible
excuse is the higher-ballot message, which must *contain* what it excuses — and it does
not, and never will, since it has already been sent. No honest node can ever construct a
depth-1 message again.

### 5.2 — R3: defeated by moving the high decision to another learner

R3 blocks the counterexample of §4 by coincidence. The partial-chaining witnesses need
value-0 history, hence lie in `Q(5)`; when the high decision is *also* learner 5's, they
are needed in its quorum, and filtering the caught ones (4 and 7) guts it.

Move the high decision to **learner 4**. `Q(4) = {3,6,8,10}` meets `Q(5)` only in
acceptor 10. Keep the low block and all three towers of §4 unchanged; replace the final
round with:

| ids | sender | priors |
|---|---|---|
| 39 | — | {} (proposal, ballot 4) |
| 40 | 10 | {39, **19**, 38} — pivot, full chain to its own round-4 message |
| 41,42,43 | 3,6,8 | {39, 38} |
| 44–47, 48–51, 52–55 | 3,6,8,10 | three further rounds |

Now acceptor 10 is forced to full-chain: if it partial-chains instead, it enters `c*`,
and `gen(4) \cup gen(5) = {10,11}` disconnects the pair, voiding the agreement claim (a
control run confirms exactly this). So the drag and the excuse obligation survive — while
the caught witnesses 4, 7, 9 now sit **outside** the final quorum, where R3 has nothing to
filter. Result under R3: low decision TRUE, high decision TRUE, `c* = {4,7,9}`, pair
connected. **Violated.**

R3 is also actively harmful. Round-4 message 20 — a member of the low decision's own W —
is attested by learner 5 at view `{}` but by **nobody** at view `{4,7}`, because `Q(5)`
contains the caught acceptors 4 and 7. So catches *disattest the value-0 side*: the
decision's own messages stop counting as payload and clause (b) dismisses them for free.
And where each learner has a unique minimal quorum, one equivocation inside `Q(l)`
silences `l` permanently.

### 5.3–5.4 — U: judging attesters at `c` instead of at their own view

This is the change `Lrns(x, Caught(x)) -> Lrns(x, c)` in clauses (b) and (c). It blocks
the nesting attacks (both counterexamples above, all four historical ones, and every
violating configuration in a 117-point sweep over carrier/witness/pivot assignments), by
exactly the mechanism self-judging disabled: an inner tower must re-prove its attestation
at the *outer* view, where the accumulated catches disconnect its carrier.

It is nonetheless **unsound**, and separately unlive. Both failures come from the same
place — a decision's messages are re-evaluated at views that did not exist when it was
made — but they are different failures and the safety one is decisive. Note that the
committed definitions call this out explicitly: self-judging is what lets "a decision's
attestation of a low-ballot 2a remain visible inside a later freshness judgment made with
a different caught set."

Both use one DAG, with a single Byzantine equivocation and everything else honest. Take
`BalToVal`: ballot 0 → value 1, ballots 1 and 2 → value 0, ballot 3 → value 1.

| ids | sender | priors | meaning |
|---|---|---|---|
| 0 | — | {} | proposal, ballot 0 (value 1) |
| 1–5 | 4,7,9,10,11 | {0} | 1bs |
| 6 | 4 | {1..5} | `x`: value-1 2a, attested by learner 5 |
| 7 | — | {} | proposal, ballot 1 (value 0) |
| 8,9,10 | 3,6,8 | {7} | clean 1bs |
| 11 | 10 | {7, 4} | 10 is in `Q(4) \cap Q(5)`, so it chains its own ballot-0 1b |
| 12 | 3 | {8,9,10,11} | `q`: value-0 2a, attested by learner 4 |
| 13 | — | {} | proposal, ballot 2 (value 0) |
| 14–18 | 4,7,9,10,11 | {13, 6, 12} | decision 1bs: they see `x`, and excuse it with `q` |
| 19–23, 24–28, 29–33 | 4,7,9,10,11 | previous round | three rounds → `D`, a depth-3 **decision** |
| 34 | 10 | {7} | the single fault: 10 equivocates |

Acceptor 10 lies in `gen(4)` but not in `gen(5)`, so catching it disconnects learner 4
from learner 5 while leaving learner 5 connected to itself. Under U, `D` is re-judged at
`{10}`: its own leaves can no longer excuse `x`, because `q`'s attester (learner 4) is
now disconnected, so **`D` loses its attestation**. Everything below follows from that.

**5.3 — the safety failure (decide, disconnect, decide the other value).** Extend the DAG
with a value-1 depth-3 tower at ballot 3 built over the decision and the fork:

| ids | sender | priors | note |
|---|---|---|---|
| 35 | — | {} | proposal, ballot 3 (value 1) |
| 36–40 | 4,7,9,10,11 | {35, 33, 34} | 1bs seeing `D` and the fork |
| 41–45, 46–50, 51–55 | 4,7,9,10,11 | previous round | three rounds → depth 3 |

```
                     attesters(D) at {10}   value-0 @ b2   value-1 @ b3
self-judged           {5}                   TRUE           FALSE   -> agreement holds
U, both clauses       {}                    TRUE           TRUE    -> VIOLATION
U, clause (b) only    {}                    TRUE           TRUE    -> VIOLATION
U, clause (c) only    {5}                   TRUE           FALSE   -> agreement holds
```

Under self-judging, `D` is still attested by learner 5, who is still connected, so `D` is
live payload at ballot 3 and clause (c) needs an excuse above ballot 2 — there is none, so
the ballot-3 tower is unfresh and the second decision cannot form. Under U, `D` is
unattested at `{10}`, so **clause (b) dismisses the decision's own messages** and the
ballot-3 tower is fresh. Learner 5 decides value 0 at ballot 2 and value 1 at ballot 3,
self-connected throughout. This is the objection in its original form: alpha decides on
the strength of another learner's attestation, that learner is later disconnected, and
alpha decides the other value.

**5.4 — the liveness failure.** Same DAG without the ballot-3 tower; instead an honest 1b
by 11 at ballot 3 over `{proposal, D, fork}`, which must excuse `x` again:

```
                     excuse attesters at {10}   honest 1b fresh?
self-judged           {5}                       TRUE   -> progress
U (either clause c)   {}                        FALSE  -> STALL
```

`D` has stopped being a usable excuse, so an honest node cannot build a fresh 1b.

### 5.5 — the split does not help

Re-judging only clause (b) — the payload clause — blocks neither nesting counterexample
*and* opens the disconnect-then-decide violation: pure harm. Re-judging only clause (c) —
the excuse clause — blocks both nesting counterexamples, keeps the disconnect violation
closed, and costs the entire liveness stall. So the protection against nesting and the
liveness cost are the same switch, and the other switch is simply unsafe.

Two further variants are ruled out without experiment. Interval-quantifying `Lrns`
(`lambda` attests at *every* view in `[Caught(p), c]`) yields a set contained in the
`c`-endpoint, so it inherits the stall a fortiori; the existential version is contained in
self-judging, so the attack survives. Letting 1bs inherit attestation from the towers that
use them — aimed at the free dismissal at the bottom of the chain — is dodged by view
curation: the innermost tower's 1b has `Tran = {22, 21, 1}`, and nothing in it builds on
message 1, so message 1 inherits nothing *there*.

**Root cause of the whole family:** inner towers are judged only at views the attacker
curates. Only judging them at the outer view defeats curation, and doing that necessarily
re-examines a decision's internals, where connectivity may have changed since.

## 6. Why this corroborates the MaxDepth rule

The nesting is not free. Measuring the view at which each excuse is *consumed*:

```
ballot-1 tower consumed at Caught = {}      ConFromCaught(5,·) = {1,2,3,4,5}
ballot-2 tower consumed at Caught = {4}     ConFromCaught(5,·) =   {2,3,4,5}
ballot-3 tower consumed at Caught = {4,7}   ConFromCaught(5,·) =     {3,4,5}
```

Strictly decreasing, and the mechanism forces it: the partial chain that thins the payload
creates a catch; the next outer view sees that catch, because the pivot's drag exposes the
witness's lower messages; and the catch disconnects the previous carrier, because the
witness sits in the previous carrier's quorum. Each nesting level therefore consumes one
connectivity state.

A strictly decreasing chain of `ConFromCaught` values is exactly `ValidSeqs(alpha)`, whose
length is `MaxDepth(alpha)`. So the attack is precisely the adversary `MaxDepth` was
designed against, it costs one `MaxDepth` level per hop, and a depth-*d* rule is beaten on
any graph with more than *d* connectivity states. `MaxDepth` is the right quantity, and
the bound is tight rather than merely sufficient.

## 7. What is and is not established

**Established.** Depth 3 is unsound for this rule on K5 — a complete counterexample,
confirmed by TLC in both freshness modes. Three repairs fail, each with a concrete
counterexample. The nesting consumes one connectivity state per level, measured.

**Not established.** "No constant depth can work" is a claim about *this rule family* on
graphs with enough connectivity states — supported by the schema (against depth *d*, use
*d* nested towers partial-chaining at rounds *d*…1) and verified at *d* = 3 on one graph.
It is not a theorem, and it is certainly not an impossibility result for protocols in
general: the attack exploits this specific freshness mechanism, and a rule built on other
machinery (explicit proof-of-history, acknowledgement rounds) need not admit it.

**Three statements one could actually prove**, in increasing ambition:

1. *Tightness of `MaxDepth` for this rule.* For every *d* there is a valid learner graph
   with connectivity-chain length > *d* and an execution in which depth-*d* decisions let
   two connected learners disagree. The upper bound is the existing `MaxDepth` proof; the
   lower bound is this counterexample schema instantiated along a graph family with
   unbounded `MaxDepth` (the K5 construction generalises to K_n). This is a lemma-sized
   piece of work and is the statement worth having.
2. *The tension theorem.* Any freshness-style rule in which attestation is evaluated at a
   single caught set, and in which an excuse valid at decision time stays valid at every
   later caught set, admits nesting at any constant depth. The clause-split result is
   direct evidence the hypotheses are the right ones. The difficulty is defining the rule
   space so the theorem is neither vacuous nor question-begging — in particular it must
   let the `MaxDepth` rule escape, which it does for a real reason: the graph runs out of
   connectivity states before the adversary runs out of levels.
3. *A protocol-general impossibility.* No evidence; do not claim it. Such a result would
   have to be an indistinguishability argument rather than a construction — each nesting
   level forces a local observer to discharge one more possible world, and a
   constant-depth local rule can discharge only constantly many — with connectivity-chain
   length playing the role failure count plays in classical round lower bounds.

---

*The counterexample DAGs, the TLA modules, and the Python model of the definitions live
on the `caught-param` branch; nothing in this document depends on them.*
