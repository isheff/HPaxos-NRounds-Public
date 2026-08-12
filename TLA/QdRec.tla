------------------------------- MODULE QdRec -------------------------------
\*   MaxQDepthInv -> cited lemma
\*   TLAPS -> SMT; proof-only
EXTENDS RecursiveWellFormed, MaxQDepthInv
LOCAL INSTANCE TLAPS

\* The pending set is exactly the next level's Qd, plus m itself when m
\* attests at the frontier: Qd ranges over the EXCLUSIVE history, pendingqd
\* over the inclusive one.
LEMMA QdRec ==
  ASSUME MessageInterfaceAssumptions,
         LearnersMightAgree, ValidLearnerGraphAssumption,
         NEW m \in Messages, NEW alpha \in DOMAIN DigestMaxQDepth(m)
  PROVE Qd(alpha, m, DigestMaxQDepth(m)[alpha] + 1)
          = DigestPendingQd(m)[alpha] \ {m}
<1>inv. MaxQDepthInvariant(m)  BY MaxQDepthInv
<1>nat. DigestMaxQDepth(m)[alpha] \in Nat
  BY <1>inv DEF MaxQDepthInvariant
<1>pd. DigestPendingQd(m)[alpha]
         = {y \in Tran(m) :
              B(y) = B(m) /\ HasDepth(alpha, y, DigestMaxQDepth(m)[alpha])}
  BY <1>inv DEF MaxQDepthInvariant
<1>ar. /\ DigestMaxQDepth(m)[alpha] + 1 > 0
       /\ (DigestMaxQDepth(m)[alpha] + 1) - 1 = DigestMaxQDepth(m)[alpha]
  BY <1>nat, SMT
<1>sub. Qd(alpha, m, DigestMaxQDepth(m)[alpha] + 1)
          \subseteq DigestPendingQd(m)[alpha] \ {m}
  <2> SUFFICES ASSUME NEW z \in Qd(alpha, m, DigestMaxQDepth(m)[alpha] + 1)
      PROVE z \in DigestPendingQd(m)[alpha] \ {m}
    OBVIOUS
  <2>1. z \in TranExclusive(m) /\ B(m) = B(z)
          /\ HasDepth(alpha, z, (DigestMaxQDepth(m)[alpha] + 1) - 1)
    BY DEF Qd
  <2>2. HasDepth(alpha, z, DigestMaxQDepth(m)[alpha])  BY <2>1, <1>ar
  <2>3. z \in Tran(m) /\ z # m  BY <2>1 DEF TranExclusive
  <2> QED BY <2>1, <2>2, <2>3, <1>pd
<1>sup. DigestPendingQd(m)[alpha] \ {m}
          \subseteq Qd(alpha, m, DigestMaxQDepth(m)[alpha] + 1)
  <2> SUFFICES ASSUME NEW z \in DigestPendingQd(m)[alpha], z # m
      PROVE z \in Qd(alpha, m, DigestMaxQDepth(m)[alpha] + 1)
    OBVIOUS
  <2>1. z \in Tran(m) /\ B(z) = B(m)
          /\ HasDepth(alpha, z, DigestMaxQDepth(m)[alpha])
    BY <1>pd
  <2>2. z \in TranExclusive(m)  BY <2>1 DEF TranExclusive
  <2>3. HasDepth(alpha, z, (DigestMaxQDepth(m)[alpha] + 1) - 1)
    BY <2>1, <1>ar
  <2> QED BY <2>1, <2>2, <2>3, <1>ar DEF Qd
<1> QED BY <1>sub, <1>sup
====================================================================
