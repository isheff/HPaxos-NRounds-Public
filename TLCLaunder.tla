-------------------------- MODULE TLCLaunder --------------------------
\* CANDIDATE COUNTEREXAMPLE to (amended) DecisionFast soundness: the
\* "connectivity laundering" scenario.  Same verified graph as TLCFast /
\* XFastCE3Graph: Acceptors {1,2,3} (1 honest); Learners {10,20,30,40};
\* Yf[10]=Yf[20]={1}, Yf[30]={2}, Yf[40]={3};
\* Q(10)=Q(20)=up{1,2,3}, Q(30)=up{2,3}, Q(40)=up{3}.
\*
\* Ballot values: 0 |-> 0 (v), everything higher |-> 1 (v').
\*
\* The scenario (ballots 0 < 1 < 2 < 3):
\*   ballot 0: full depth-2 fast cert for learner 10 (WR/WG/WF as in TLCFast).
\*   ballot 1: XC3 = 3's 1b that CHAINS TO ITS OWN WR3 but omits WG3/WF3
\*             (the "chained omitter" -- absent from all previous TLC pools);
\*             XP2 = 2a atop {XC3} carrying 40 (Q(40)=up{3} is Byz-forgeable).
\*   ballot 2: XR1 = 2's 1b referencing WG2 (its own width msg) + XP2.
\*             In XR1's SMALL view no fork of 3 is visible (WR3 -> XC3 chain),
\*             so 40 is still connected and XP2 excuses the WG2 conflict:
\*             Fresh(30, XR1) = TRUE ("laundering").
\*             XD3 = 3's clean 1b; XP1 = 2a atop {XR1, XD3} carrying 30.
\*   ballot 3: XRA = honest 1's 1b referencing WF1 (the whole cert) + XP1.
\*             In XRA's view 3 IS caught (WG3 vs XC3/XD3), so 40 is dead --
\*             but XP1 carries 30, whose safety set {1,2} is untouched, so
\*             XP1 excuses every width conflict: Fresh(20, XRA) = TRUE.
\*   ballot 3 high side: XRB/XRC 1bs, YG* width 2as, YF* cert tops => a
\*             depth-2 fast cert for learner 20 at ballot 3.
\*
\* If NoViolation FAILS: DecisionFast(m,10,0) /\ DecisionFast(m,20,3)
\* /\ 10 still connected to 20 in the closure /\ BalToVal(0) # BalToVal(3)
\* -- i.e. AgreementM as stated is FALSE.
EXTENDS Naturals, FiniteSets, TLC

Acceptors == {1, 2, 3}
Learners  == {10, 20, 30, 40}
Yf == [l \in Learners |-> CASE l = 10 -> {1} [] l = 20 -> {1}
                            [] l = 30 -> {2} [] l = 40 -> {3}]
Yg == [l \in Learners |-> CASE l = 10 -> {1,2,3} [] l = 20 -> {1,2,3}
                            [] l = 30 -> {2,3}   [] l = 40 -> {3}]
Quorums(l)    == {q \in SUBSET Acceptors : Yg[l] \subseteq q}
SafetySets(p) == {s \in SUBSET Acceptors : (UNION {Yf[x] : x \in p}) \subseteq s}
ConFromCaught(alpha, caught) ==
  {beta \in Learners : \E s \in SafetySets({alpha, beta}) : (s \cap caught) = {}}
\* Ballot values: 0 |-> v=0; 1,2,3 |-> v'=1; above 3, alternate so that
\* AlwaysAHigherBallot (every value recurs unboundedly) is satisfiable:
\* value 0 recurs on even ballots >= 4, value 1 on odd ballots.
BalToVal(b) == IF b = 0 THEN 0 ELSE IF b <= 3 THEN 1 ELSE b % 2

\* --- messages (nested records; priors are the direct references) --------
\* sender 0 = the (non-acceptor) proposer.
WP0 == [sender |-> 0, prop |-> TRUE, pb |-> 0, priors |-> {}]
WR1 == [sender |-> 1, prop |-> FALSE, pb |-> 0, priors |-> {WP0}]
WR2 == [sender |-> 2, prop |-> FALSE, pb |-> 0, priors |-> {WP0}]
WR3 == [sender |-> 3, prop |-> FALSE, pb |-> 0, priors |-> {WP0}]
WG1 == [sender |-> 1, prop |-> FALSE, pb |-> 0, priors |-> {WR1, WR2, WR3}]
WG2 == [sender |-> 2, prop |-> FALSE, pb |-> 0, priors |-> {WR1, WR2, WR3}]
WG3 == [sender |-> 3, prop |-> FALSE, pb |-> 0, priors |-> {WR1, WR2, WR3}]
WF1 == [sender |-> 1, prop |-> FALSE, pb |-> 0, priors |-> {WG1, WG2, WG3}]
WF2 == [sender |-> 2, prop |-> FALSE, pb |-> 0, priors |-> {WG1, WG2, WG3}]
WF3 == [sender |-> 3, prop |-> FALSE, pb |-> 0, priors |-> {WG1, WG2, WG3}]
\* ballot 1: the chained-omitter 1b + the 40-carrier fork
WP1 == [sender |-> 0, prop |-> TRUE, pb |-> 1, priors |-> {WP0}]
XC3 == [sender |-> 3, prop |-> FALSE, pb |-> 0, priors |-> {WP1, WR3}]
XP2 == [sender |-> 3, prop |-> FALSE, pb |-> 0, priors |-> {XC3}]
\* ballot 2: the laundering 1b + the 30-carrier
WP2 == [sender |-> 0, prop |-> TRUE, pb |-> 2, priors |-> {WP1}]
XR1 == [sender |-> 2, prop |-> FALSE, pb |-> 0, priors |-> {WG2, XP2, WP2}]
XD3 == [sender |-> 3, prop |-> FALSE, pb |-> 0, priors |-> {WP2}]
XP1 == [sender |-> 2, prop |-> FALSE, pb |-> 0, priors |-> {XR1, XD3}]
\* ballot 3: honest 1's high 1b + the high-side fast cert for 20
WP3 == [sender |-> 0, prop |-> TRUE, pb |-> 3, priors |-> {WP2}]
XRA == [sender |-> 1, prop |-> FALSE, pb |-> 0, priors |-> {WF1, XP1, WP3}]
XRB == [sender |-> 2, prop |-> FALSE, pb |-> 0, priors |-> {XR1, WP3}]
XRC == [sender |-> 3, prop |-> FALSE, pb |-> 0, priors |-> {WP3}]
YG1 == [sender |-> 1, prop |-> FALSE, pb |-> 0, priors |-> {XRA, XRB, XRC}]
YG2 == [sender |-> 2, prop |-> FALSE, pb |-> 0, priors |-> {XRA, XRB, XRC}]
YG3 == [sender |-> 3, prop |-> FALSE, pb |-> 0, priors |-> {XRA, XRB, XRC}]
YF1 == [sender |-> 1, prop |-> FALSE, pb |-> 0, priors |-> {YG1, YG2, YG3}]
YF2 == [sender |-> 2, prop |-> FALSE, pb |-> 0, priors |-> {YG1, YG2, YG3}]
YF3 == [sender |-> 3, prop |-> FALSE, pb |-> 0, priors |-> {YG1, YG2, YG3}]

AllMsgs == {WP0, WR1, WR2, WR3, WG1, WG2, WG3, WF1, WF2, WF3,
            WP1, XC3, XP2, WP2, XR1, XD3, XP1,
            WP3, XRA, XRB, XRC, YG1, YG2, YG3, YF1, YF2, YF3}

\* --- Tran / ballot / value ----------------------------------------------
RECURSIVE TranOf(_)
TranOf(m) == {m} \cup UNION {TranOf(p) : p \in m.priors}
Tran(m)   == TranOf(m)
TranExcl(m) == Tran(m) \ {m}

IsProposal(m) == m.prop
B(m) == LET ps == {x \in Tran(m) : x.prop} IN
        IF ps = {} THEN 0 ELSE CHOOSE b \in {x.pb : x \in ps} :
                                 \A x \in ps : x.pb <= b
V(m) == BalToVal(B(m))
SigS(S) == {x.sender : x \in S}

CaughtS(S) == {a \in Acceptors :
  \E m1 \in S : \E m2 \in S :
    /\ m1.sender = a /\ m2.sender = a
    /\ m1 \notin Tran(m2) /\ m2 \notin Tran(m1)}
Caught(m)  == CaughtS(Tran(m))
Con(alpha, m) == ConFromCaught(alpha, Caught(m))

IsOneB(m) == /\ ~IsProposal(m)
             /\ Cardinality({x \in Tran(m) : B(x) = B(m)}) = 2

\* --- HasDepth / Qd / Lrns / Fresh ----------------------------------------
RECURSIVE HasDepth(_,_,_)
RECURSIVE Lrns(_)
RECURSIVE Fresh(_,_)

Qd(l, m, d) == {x \in TranExcl(m) : B(x) = B(m) /\ HasDepth(l, x, d-1)}

HasDepth(l, m, d) ==
  /\ m.sender \in Acceptors
  /\ IF d = 0 THEN IsOneB(m) /\ Fresh(l, m)
              ELSE SigS(Qd(l, m, d)) \in Quorums(l)

Lrns(m) == {l \in Learners : HasDepth(l, m, 1)}

Fresh(alpha, m) ==
  \A x \in Tran(m) :
    \/ V(x) = V(m)
    \/ (Con(alpha, m) \cap Lrns(x)) = {}
    \/ \E p \in TranExcl(m) : B(p) > B(x) /\ (Con(alpha, m) \cap Lrns(p)) # {}

\* --- decisions ----------------------------------------------------------
TranClosure(S) == UNION {Tran(x) : x \in S}

DecisionFast(m, alpha, b) ==
  \E s \in SUBSET {x \in TranClosure(m) : B(x) = b} :
    LET L == {alpha} \cup UNION {Con(alpha, x) : x \in s}
    IN /\ \A l \in L : SigS(s) \in Quorums(l)
       /\ \A x \in s :
            /\ L \subseteq Lrns(x)
            /\ \A l \in L :
                 SigS({y \in TranExcl(x) : B(y) = b /\ L \subseteq Lrns(y)}) \in Quorums(l)

\* ===================================================================
\* The checks
\* ===================================================================
CL == TranClosure(AllMsgs)

ChkCaughtXR1   == Caught(XR1)          \* expect {}   (3 chained via WR3->XC3)
ChkFresh30XR1  == Fresh(30, XR1)       \* expect TRUE  (the laundering step)
ChkLrnsXP2     == Lrns(XP2)            \* expect {40}
ChkLrnsXP1     == Lrns(XP1)            \* expect >= {30}
ChkCaughtXRA   == Caught(XRA)          \* expect {3}  (WG3 vs XC3/XD3 visible)
ChkCon20XRA    == Con(20, XRA)         \* expect {10,20,30} (40 dead, 30 alive)
ChkIsOneBXRA   == IsOneB(XRA)          \* expect TRUE
ChkFresh20XRA  == Fresh(20, XRA)       \* expect TRUE  <- THE SEED
ChkFresh10XRA  == Fresh(10, XRA)       \* expect TRUE
ChkCaughtCL    == CaughtS(CL)          \* expect {2,3} (1 stays clean)
ChkConnected   == 10 \in ConFromCaught(20, CaughtS(CL))  \* expect TRUE
ChkFastLow     == DecisionFast(AllMsgs, 10, 0)           \* expect TRUE
ChkFastHigh    == DecisionFast(AllMsgs, 20, 3)           \* expect TRUE
\* consistency with the PROVEN slow case: the low cert must be depth-2 only
\* (MaxDepth(10) = 3 in this graph, so no DecisionSlow at ballot 0 => no
\* contradiction with the machine-verified TraceExistenceSlow machinery).
ChkDepth2WF1   == \A l \in Learners : HasDepth(l, WF1, 2)  \* expect TRUE
ChkDepth3WF1   == HasDepth(10, WF1, 3)                     \* expect FALSE

AgreementViolation ==
  /\ ChkFastLow
  /\ ChkFastHigh
  /\ ChkConnected
  /\ BalToVal(0) # BalToVal(3)

Sanity == /\ PrintT(<< "Caught(XR1)    =", ChkCaughtXR1 >>)
          /\ PrintT(<< "Fresh(30,XR1)  =", ChkFresh30XR1 >>)
          /\ PrintT(<< "Lrns(XP2)      =", ChkLrnsXP2 >>)
          /\ PrintT(<< "Lrns(XP1)      =", ChkLrnsXP1 >>)
          /\ PrintT(<< "Caught(XRA)    =", ChkCaughtXRA >>)
          /\ PrintT(<< "Con(20,XRA)    =", ChkCon20XRA >>)
          /\ PrintT(<< "IsOneB(XRA)    =", ChkIsOneBXRA >>)
          /\ PrintT(<< "Fresh(20,XRA)  =", ChkFresh20XRA >>)
          /\ PrintT(<< "Fresh(10,XRA)  =", ChkFresh10XRA >>)
          /\ PrintT(<< "CaughtS(CL)    =", ChkCaughtCL >>)
          /\ PrintT(<< "10-20 connected=", ChkConnected >>)
          /\ PrintT(<< "FastLow(10,0)  =", ChkFastLow >>)
          /\ PrintT(<< "FastHigh(20,3) =", ChkFastHigh >>)
          /\ PrintT(<< "Depth2(WF1)all =", ChkDepth2WF1 >>)
          /\ PrintT(<< "Depth3(WF1,10) =", ChkDepth3WF1 >>)
          /\ PrintT(<< "VIOLATION      =", AgreementViolation >>)

NoViolation == ~AgreementViolation

VARIABLE done
Init == done = FALSE /\ Sanity
Next == done' = done
Spec == Init /\ [][Next]_done
====================================================================
