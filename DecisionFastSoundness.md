# DecisionFast soundness — REFUTED (machine-checked counterexample)

**Status (this session):** `DecisionFast` (including the same-ballot `B(y)=b`
amendment) is **UNSOUND**, and therefore **`AgreementM` as stated is FALSE.**
The counterexample is machine-checked: the learner graph is TLAPS-verified
(`XFastCE3Graph.tla`, full `LearnerGraphAssumptions` + `MaxDepth(10) >= 3`)
and the message DAG + violation are TLC-verified (`TLCLaunder.tla` — TLC
reports `Error: The invariant of NoViolation is equal to FALSE`).

This reverses the previous handoff's headline ("soundness holds, strongly
supported"). The previous TLC evidence was clean only because every fork pool
missed one message shape (§3). The "core open problem" flagged in the old §6.2
(descent learners are only connected *as of the citing 1b*, not as of `rstar`)
was not a proof-bookkeeping gap — it is a real, exploitable attack.

---

## 1. The counterexample (`TLCLaunder.tla`) — "connectivity laundering"

**Graph** (= `XFastCE3Graph.tla`, TLAPS-verified): Acceptors `{1,2,3}`
(1 honest); Learners `{10,20,30,40}`; safety generators `Yf[10]=Yf[20]={1}`,
`Yf[30]={2}`, `Yf[40]={3}` (so `SafetySets({x,y})` = up-closure of
`Yf[x] ∪ Yf[y]`); quorum generators `Q(10)=Q(20)=up{1,2,3}`, `Q(30)=up{2,3}`,
`Q(40)=up{3}` (note: 30- and 40-quorums are Byzantine-forgeable).
`BalToVal`: ballot 0 ↦ value 0 (call it `v`); ballots 1,2,3 ↦ value 1 (`v'`)
(recurring on higher ballots so `AlwaysAHigherBallot` holds).

**Messages** (27 total; `X*` are the new shapes):

| ballot | messages |
|---|---|
| 0 | `WP0` prop; `WR1-3` 1bs; `WG1-3` width 2as (all-L-good); `WF1-3` cert tops. Fast cert: `s = {WF1,WF2,WF3}`, `L = {10,20,30,40}` (each `Caught(WFa) = {}` so `Con(10,WFa)` = all). `DecisionFast(m,10,0)` = TRUE. Depth-2 only (`HasDepth(10,WF1,3)` = FALSE) — genuinely fast, not slow. |
| 1 | `XC3` = 3's **chained omitter** 1b: priors `{WP1, WR3}` — chains to 3's own pre-width 1b `WR3`, omits `WG3/WF3`. Fresh (its view has no L-good conflict). `XP2` = 2a atop `{XC3}` carrying 40 (`SigS={3} ∈ Q(40)`). |
| 2 | `XR1` = 2's **laundering** 1b: priors `{WG2, XP2, WP2}` — builds on 2's *own* width message `WG2` (so 2 stays uncaught in every view that matters) and cites `XP2`. In `Tran(XR1)`, 3's messages are `WR3 → XC3` (chained): **`Caught(XR1) = {}`**, so 40 is still connected and `XP2` excuses the `WG2` conflict: **`Fresh(30, XR1)` = TRUE.** `XD3` = 3's clean 1b; `XP1` = 2a atop `{XR1, XD3}` carrying 30 (`SigS={2,3} ∈ Q(30)`). |
| 3 | `XRA` = honest 1's 1b: priors `{WF1, XP1, WP3}`. Its view holds the whole width (via `WF1`) *and* `XC3/XD3` (via `XP1`), so **`Caught(XRA) = {3}`** and 40 is dead — but `XP1` carries 30, and `SafetySets({20,30}) = up{1,2}` is untouched: `Con(20, XRA) = {10,20,30}`, and `XP1` excuses every width conflict. **`Fresh(20, XRA)` = `Fresh(10, XRA)` = TRUE.** High-side cert for 20 at ballot 3: 1bs `XRA/XRB/XRC`, width `YG1-3`, tops `YF1-3` ⇒ `DecisionFast(m,20,3)` = TRUE with `L' = {10,20,30}`. |

**Closure:** `CaughtS(closure) = {2,3}` (2 forks `WF2` vs `XR1` in the full
closure — harmless, since only acceptor 1 backs the 10–20 connection), so
`10 ∈ ConFromCaught(20, CaughtS(closure))`. Hence

```
Decision(m,10,0) ∧ Decision(m,20,3) ∧ 10 ∈ ConFromCaught(20, CaughtS(TranClosure(m)))
∧ BalToVal(0) = 0 ≠ 1 = BalToVal(3)      — AgreementM VIOLATED.
```

TLC-confirmed sub-facts (all match hand analysis): `Caught(XR1)={}`,
`Fresh(30,XR1)=T`, `Lrns(XP2)={40}`, `Lrns(XP1)⊇{30}`, `Caught(XRA)={3}`,
`Con(20,XRA)={10,20,30}`, `IsOneB(XRA)=T`, `Fresh(20,XRA)=T`, `Fresh(10,XRA)=T`,
`CaughtS(CL)={2,3}`, both `DecisionFast`s TRUE, depth-2-not-3 TRUE/FALSE.

## 2. The mechanism, in one paragraph

Freshness excuses are judged against `Con(gamma, r)` computed from the
**citing 1b's own view** `Caught(r)`. The depth-2 cert forces (via the
uncaught shared signer of a width/quorum intersection) exactly **one** width
message into an intermediate 1b's view — the signer's own — and one message
has no quorum to re-intersect. So a Byzantine acceptor backing some learner's
safety set (3 backing 40) forks *between the width layer and its ballot-1 1b*:
the fork is visible only in views containing the full width (e.g. `rstar`'s),
not in the small view of `XR1`, which references just its own width message.
`XR1` is then legitimately fresh — the sacrificed learner 40 is still alive
*in its view* — and the carrier `XP1` on top of it carries a *different*
learner (30) whose safety set `{1,2}` is honest-backed and survives into the
top view. One learner is sacrificed per intermediate ballot; the width
conflict is laundered through the chain. The old mutual-witnessing intuition
("a 1b omitting a width message has a caught signer ⇒ the fork's learner
disconnects") is **level-confused**: the disconnection happens as of the top
view, but the excuse that needs the learner is judged one level down, where
the fork is invisible. This is precisely why `WidthUnexcusableStep` was
false — and the failure is essential, not an invariant artifact.

Consistency notes (why this contradicts no machine-verified lemma):
- `WidthUnexcusableBase` (no BadOneB at `lobal+1`, proven) — `XC3` at
  `lobal+1` is *not* a `BadOneB` (its view holds no L-good conflict); the
  escape lives strictly above the base case, needing ≥ 2 intermediate ballots.
  (With `hibal = lobal+2` every variant dies — hand-checked.)
- The slow case is untouched: the cert is depth-2 but `MaxDepth(10)=3`, so
  `DecisionSlow(m,10,0)` is FALSE; `TraceExistenceSlow`/`TraceContradiction`
  don't apply. The countermodel instead **falsifies** the OMITTED
  `TraceExistenceFast`, and with it `WidthUnexcusable`,
  `FreshDescentImpossible`, `AgreementCaseFast` (witness:
  `BadOneB(20, XRA, 0)` holds at ballot 3).

## 3. Why five earlier TLC models all ran clean

Their pools contained (i) *clean omitters* (⇒ signer caught as soon as the
width is visible ⇒ its learner dies), (ii) *build-on-width 1bs at `lobal+1`*
(⇒ see the conflict with an empty excuse interval ⇒ not fresh), and (iii)
chained omitters + carriers — **but the checked high 1b always referenced
pool elements directly**, so every quorum-1b's fork was visible in the
checking view. The laundering needs a *relay*: the high 1b references only
the ballot-2 carrier `XP1`, whose quorum-1b `XR1` has a small view hiding the
ballot-1 fork, with the acceptor roles *split* (2 = backer of the surviving
learner builds-on-width at ballot 2; 3 = backer of the sacrificed learner
chain-omits at ballot 1). No pool composed that.

## 4. Status of the TLAPS artifacts

- `MessageInterface.tla` — still 70/70 with `TraceExistenceFast` OMITTED;
  that lemma is now **known FALSE** (not merely unproven), so `AgreementCaseLt`
  / `AgreementM` are unsound as stated. The SLOW case and all other lemmas
  are unaffected.
- `XFastProof.tla` — A1–A7, `FastSqueeze`, `FreshForcesCarrier`,
  `CarrierBelowOneB`, `WidthUnexcusableBase` remain true and proven.
  `WidthUnexcusableStep` (OMITTED) is false; `WidthUnexcusable`,
  `FreshDescentImpossible`, `AgreementCaseFast` are **false** (they rested on
  it, and `TLCLaunder` witnesses their negations). Do not attempt to prove
  them.
- `TLCLaunder.tla` (+ `.cfg`) — **the countermodel.** Run:
  `java -cp <tla2tools.jar> tlc2.TLC -deadlock TLCLaunder.tla`; the invariant
  `NoViolation` fails, printing all sub-facts. ~50 s.
- `XFastCE3Graph.tla` — TLAPS-verified `LearnerGraphAssumptions` +
  `MaxDepth(10) >= 3` for the countermodel's graph (this file is what makes
  the refutation machine-checked on the graph side).

## 5. Repair options — **RESOLVED: option 1 taken (2026-07-16, user decision)**

`Decision(m,a,b) == DecisionSlow(m,a,b)` now (fast path dropped from
`Decision`; `DecisionFast` stays defined as the refuted rule's record).
`TraceExistenceFast` deleted; `DecisionHighWitness` and `AgreementCaseLt`
lost their fast branches; `AgreementM` is now fully proven with **zero
OMITTED lemmas** in `MessageInterface.tla`.

The options considered were:

1. **Drop the fast path**: `Decision(m,a,b) == DecisionSlow(m,a,b)`. Then
   `AgreementM` follows immediately from the already-verified machinery
   (delete the fast branch of `AgreementCaseLt` and `TraceExistenceFast`).
   Smallest change; loses the feature.  **<- taken**
2. **Deepen the cert**: require per-learner depth-`MaxDepth(l)` towers for
   every `l ∈ L` (i.e. `DecisionSlow`-for-every-connected-learner at one
   ballot). Hand analysis: depth-3 kills this countermodel's shape (the
   ballot-1 1b must either omit a sub-width message — caught *in `XR1`'s
   view* — or build on one — unexcusable at ballot 1); conjecture: depth
   `MaxDepth` is exactly what's needed, since `MaxDepth` bounds the
   Con-degradation chain that the laundering consumes (one learner per
   level). Cost: same message depth as slow, so it is no longer "fast";
   benefit over slow: unclear. Needs a real proof (adapt
   `TraceExistenceSlow` per-learner).
3. **Restrict the learner-graph class**: the attack needs a learner (40)
   whose every safety set with the rest of `L` dies as of `rstar` while some
   dies only *there* — impossible if e.g. all relevant pairs' safety sets
   share a common honest core (the original G(N) intuition, where acceptor 1
   is in every safety set that matters AND every quorum). A class axiom like
   "some safety set of every pair is contained in every quorum" would
   restore mutual witnessing at every level, but it is very restrictive and
   graph-dependent.

**Do not** resume the §6-style width-quorum induction: its missing step is
now known unprovable.

## 6. Definitions (unchanged, for reference)

Messages form a finite acyclic DAG via `Tran`; `B(m)` = max proposal ballot
in `Tran(m)`; `V(m) = BalToVal(B(m))`; `CaughtS(S)` = acceptors with two
`Tran`-incomparable messages in `S`; `Caught(m) = CaughtS(Tran(m))`;
`Con(a,m) = ConFromCaught(a, Caught(m))`;
`IsOneB(m) == ~IsProposal(m) /\ Cardinality({x ∈ Tran(m): B(x)=B(m)}) = 2`;
`HasDepth(a,m,0) == IsOneB(m) /\ Fresh(a,m)`, `HasDepth(a,m,d>0)` = an
`a`-quorum `Qd(a,m,d)` of same-ballot depth-`d-1` messages below `m`;
`Lrns(m) == {a : HasDepth(a,m,1)}`.

```
Fresh(alpha, m) ==
  \A x \in Tran(m) :
    \/ V(x) = V(m)
    \/ Con(alpha, m) \cap Lrns(x) = {}
    \/ \E p \in TranExclusive(m) : B(p) > B(x) /\ Con(alpha, m) \cap Lrns(p) # {}

DecisionFast(m, alpha, b) ==   \* the (amended) rule REFUTED here
  \E s \in SUBSET {x \in TranClosure(m) : B(x) = b} :
  LET L == ({alpha} \cup UNION {Con(alpha, x) : x \in s})
   IN /\ \A l \in L : SigS(s) \in Quorums(l)
      /\ \A x \in s :
         /\ L \subseteq Lrns(x)
         /\ \A l \in L :
            SigS({y \in TranExclusive(x) : B(y) = b /\ L \subseteq Lrns(y)}) \in Quorums(l)
```

Learner graph: `SafetySets`/`Quorums` upward-closed;
`ValidLearnerGraphAssumption` (`s ∩ qx ∩ qy ≠ {}`),
`CondensedLearnerGraphAssumption` (`xy ∪ yz ∈ SafetySets({x,z})`);
`ConFromCaught(a, C)` antitone in `C`.

## 7. History (superseded analyses, kept for the record)

- The pre-refutation handoff claimed soundness via "mutual witnessing", with
  six clean TLC models (`TLCFast/TLCSearch/TLCSweep/TLCGap/TLCDeep/TLCClean`)
  and a proof plan whose one open step (`WidthUnexcusableStep`) was known
  false-as-stated but believed fixable by carrying the full width quorum.
  §2–§3 above explain both why the step is unfixable and why those models
  missed the attack.
- Older discarded files: `XFastCE.tla`, `XFastCE3.tla` (failed counterexample
  attempts — they made the honest node see the forks directly),
  `XFastSoundness.tla`, `XFastDepth3.tla`, `XCounterexample.tla` (old-rule
  countermodel at MaxDepth 2).
