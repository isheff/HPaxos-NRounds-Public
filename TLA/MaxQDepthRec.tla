---------------------------- MODULE MaxQDepthRec ----------------------------
\*   MaxQDepthInv, AttesterInherit, HasDepthDownward, TranSubMessages
\*     -> cited lemmas
\*   TLAPS -> SMT; proof-only
EXTENDS RecursiveWellFormed, MaxQDepthInv, AttesterInherit, HasDepthDownward,
        TranSubMessages
LOCAL INSTANCE TLAPS

\* The own-HasDepth reading of the stored frontier, for acceptor-signed m:
\* m attests at depth d >= 1 exactly when its learner's frontier exists, is
\* at least 1, and dominates d. (Downward-closure of depths >= 1 plus
\* inheritance of any frontier attester's quorum make every 1..frontier
\* level attested; anything above the frontier would bump it.)
LEMMA MaxQDepthRec ==
  ASSUME MessageInterfaceAssumptions,
         LearnersMightAgree, ValidLearnerGraphAssumption,
         NEW m \in Messages, Sig(m) \in Acceptors,
         NEW alpha \in Learners, NEW d \in Nat, d >= 1
  PROVE HasDepth(alpha, m, d) <=>
          (/\ alpha \in DOMAIN MemoMaxQDepth(m)
           /\ MemoMaxQDepth(m)[alpha] >= 1
           /\ d <= MemoMaxQDepth(m)[alpha])
<1>tok. TypeOKMessageInterface  BY DEF MessageInterfaceAssumptions
<1>tf. TranFinite  BY DEF MessageInterfaceAssumptions
<1>tt. TranTrans  BY DEF MessageInterfaceAssumptions
<1>ta. TranAcyclic  BY DEF MessageInterfaceAssumptions
<1>inv. MaxQDepthInvariant(m)  BY MaxQDepthInv
<1>mT. m \in Tran(m)  BY DEF Tran
<1>fwd. HasDepth(alpha, m, d) =>
          (/\ alpha \in DOMAIN MemoMaxQDepth(m)
           /\ MemoMaxQDepth(m)[alpha] >= 1
           /\ d <= MemoMaxQDepth(m)[alpha])
  <2>1. CASE HasDepth(alpha, m, d)
    <3>dom. alpha \in DOMAIN MemoMaxQDepth(m)
      <4>1. alpha \in {a2 \in Learners :
                         \E y \in Tran(m) :
                           B(y) = B(m) /\ \E dd \in Nat : HasDepth(a2, y, dd)}
        BY <2>1, <1>mT
      <4> QED BY <4>1, <1>inv DEF MaxQDepthInvariant
    <3>le. d <= MemoMaxQDepth(m)[alpha]
      BY <2>1, <3>dom, <1>mT, <1>inv DEF MaxQDepthInvariant
    <3>nat. MemoMaxQDepth(m)[alpha] \in Nat
      BY <3>dom, <1>inv DEF MaxQDepthInvariant
    <3>ge. MemoMaxQDepth(m)[alpha] >= 1  BY <3>le, <3>nat, SMT
    <3> QED BY <3>dom, <3>le, <3>ge
  <2> QED BY <2>1
<1>bwd. (/\ alpha \in DOMAIN MemoMaxQDepth(m)
         /\ MemoMaxQDepth(m)[alpha] >= 1
         /\ d <= MemoMaxQDepth(m)[alpha])
        => HasDepth(alpha, m, d)
  <2>1. CASE /\ alpha \in DOMAIN MemoMaxQDepth(m)
             /\ MemoMaxQDepth(m)[alpha] >= 1
             /\ d <= MemoMaxQDepth(m)[alpha]
    <3>nat. MemoMaxQDepth(m)[alpha] \in Nat
      BY <2>1, <1>inv DEF MaxQDepthInvariant
    <3>att. PICK y \in Tran(m) :
              B(y) = B(m) /\ HasDepth(alpha, y, MemoMaxQDepth(m)[alpha])
      BY <2>1, <1>inv DEF MaxQDepthInvariant
    <3>top. HasDepth(alpha, m, MemoMaxQDepth(m)[alpha])
      <4>a. CASE y = m
        <5> QED BY <4>a, <3>att
      <4>b. CASE y # m
        <5>1. y \in TranExclusive(m)  BY <4>b DEF TranExclusive
        <5> QED BY <5>1, <3>att, <2>1, <3>nat,
                  <1>tok, <1>tt, <1>tf, <1>ta, AttesterInherit
      <4> QED BY <4>a, <4>b
    <3> QED
      BY <3>top, <2>1, <3>nat,
         <1>tok, <1>tt, <1>tf, <1>ta, HasDepthDownward
  <2> QED BY <2>1
<1> QED BY <1>fwd, <1>bwd
====================================================================
