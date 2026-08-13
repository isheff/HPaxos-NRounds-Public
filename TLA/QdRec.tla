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
         NEW m \in Messages, NEW alpha \in DOMAIN MemoMaxQDepth(m)
  PROVE Qd(alpha, m, MemoMaxQDepth(m)[alpha] + 1)
          = MemoPendingQd(m)[alpha] \ {m}
<1>inv. MaxQDepthInvariant(m)  BY MaxQDepthInv
<1>nat. MemoMaxQDepth(m)[alpha] \in Nat
  BY <1>inv DEF MaxQDepthInvariant
<1>pd. MemoPendingQd(m)[alpha]
         = {y \in Tran(m) :
              B(y) = B(m) /\ HasDepth(alpha, y, MemoMaxQDepth(m)[alpha])}
  BY <1>inv DEF MaxQDepthInvariant
<1>ar. /\ MemoMaxQDepth(m)[alpha] + 1 > 0
       /\ (MemoMaxQDepth(m)[alpha] + 1) - 1 = MemoMaxQDepth(m)[alpha]
  BY <1>nat, SMT
<1>sub. Qd(alpha, m, MemoMaxQDepth(m)[alpha] + 1)
          \subseteq MemoPendingQd(m)[alpha] \ {m}
  <2> SUFFICES ASSUME NEW z \in Qd(alpha, m, MemoMaxQDepth(m)[alpha] + 1)
      PROVE z \in MemoPendingQd(m)[alpha] \ {m}
    OBVIOUS
  <2>1. z \in TranExclusive(m) /\ B(m) = B(z)
          /\ HasDepth(alpha, z, (MemoMaxQDepth(m)[alpha] + 1) - 1)
    BY DEF Qd
  <2>2. HasDepth(alpha, z, MemoMaxQDepth(m)[alpha])  BY <2>1, <1>ar
  <2>3. z \in Tran(m) /\ z # m  BY <2>1 DEF TranExclusive
  <2> QED BY <2>1, <2>2, <2>3, <1>pd
<1>sup. MemoPendingQd(m)[alpha] \ {m}
          \subseteq Qd(alpha, m, MemoMaxQDepth(m)[alpha] + 1)
  <2> SUFFICES ASSUME NEW z \in MemoPendingQd(m)[alpha], z # m
      PROVE z \in Qd(alpha, m, MemoMaxQDepth(m)[alpha] + 1)
    OBVIOUS
  <2>1. z \in Tran(m) /\ B(z) = B(m)
          /\ HasDepth(alpha, z, MemoMaxQDepth(m)[alpha])
    BY <1>pd
  <2>2. z \in TranExclusive(m)  BY <2>1 DEF TranExclusive
  <2>3. HasDepth(alpha, z, (MemoMaxQDepth(m)[alpha] + 1) - 1)
    BY <2>1, <1>ar
  <2> QED BY <2>1, <2>2, <2>3, <1>ar DEF Qd
<1> QED BY <1>sub, <1>sup
====================================================================
