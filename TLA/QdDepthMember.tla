-------------------------- MODULE QdDepthMember --------------------------
EXTENDS MessageInterface

\* Qd membership yields depth at ANY index e explicitly equated to d - 1.
\* The explicit e parameter makes the goal-side match first-order: backends
\* abstract compound arithmetic inside opaque applications, so matching a
\* plain parameter e and separately discharging e = d - 1 succeeds where
\* recognizing HasDepth(_, _, D - k + 1 - 1) as an instance would fail.
LEMMA QdDepthMember ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         NEW alpha \in Learners, NEW x \in Messages,
         NEW d \in Nat, d >= 1,
         NEW y \in Qd(alpha, x, d),
         NEW e, e = d - 1
  PROVE HasDepth(alpha, y, e)
<1>1. HasDepth(alpha, y, d - 1)  BY DEF Qd
<1> QED BY <1>1
====================================================================
