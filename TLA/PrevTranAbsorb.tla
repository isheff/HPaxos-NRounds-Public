-------------------------- MODULE PrevTranAbsorb --------------------------
\*   TranExclusiveInduction, PrevTranRec, DeepestKnownInv -> cited lemmas
\*   TLAPS -> proof-only
EXTENDS RecursiveWellFormed, TranExclusiveInduction, PrevTranRec,
        DeepestKnownInv
LOCAL INSTANCE TLAPS

\* Induction motive, module-level so TranExclusiveInduction can instantiate
\* it by name.
PrevTranAbsorbP(z) ==
  \A y \in PrevTran(z) : PrevTran(y) \subseteq PrevTran(z)

\* Chains absorb their members' chains: anything on z's chain carries a
\* chain that is a suffix of z's.
LEMMA PrevTranAbsorb ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         NEW m \in Messages
  PROVE \A y \in PrevTran(m) : PrevTran(y) \subseteq PrevTran(m)
<1>cl. \A x \in Messages :
         (\A yy \in TranExclusive(x) : PrevTranAbsorbP(yy)) => PrevTranAbsorbP(x)
  <2> SUFFICES ASSUME NEW x \in Messages,
                      \A yy \in TranExclusive(x) : PrevTranAbsorbP(yy)
      PROVE PrevTranAbsorbP(x)
    OBVIOUS
  <2>rec. PrevTran(x) = {x} \cup (IF Sig(x) \in DOMAIN DeepestKnown(x)
                                    THEN PrevTran(DeepestKnown(x)[Sig(x)][2].id)
                                    ELSE {})
    BY PrevTranRec
  <2>a. CASE Sig(x) \notin DOMAIN DeepestKnown(x)
    <3>1. PrevTran(x) = {x}  BY <2>rec, <2>a
    <3> QED BY <3>1 DEF PrevTranAbsorbP
  <2>b. CASE Sig(x) \in DOMAIN DeepestKnown(x)
    <3> DEFINE z1 == DeepestKnown(x)[Sig(x)][2].id
    <3>inv. DeepestKnownInvariant(x)  BY DeepestKnownInv
    <3>z1. z1 \in TranExclusive(x)
      BY <3>inv, <2>b DEF DeepestKnownInvariant
    <3>ih. PrevTranAbsorbP(z1)  BY <3>z1
    <3>pt. PrevTran(x) = {x} \cup PrevTran(z1)  BY <2>rec, <2>b
    <3> SUFFICES ASSUME NEW y \in PrevTran(x)
        PROVE PrevTran(y) \subseteq PrevTran(x)
      BY DEF PrevTranAbsorbP
    <3>a2. CASE y = x
      <4> QED BY <3>a2
    <3>b2. CASE y \in PrevTran(z1)
      <4>1. PrevTran(y) \subseteq PrevTran(z1)
        BY <3>b2, <3>ih DEF PrevTranAbsorbP
      <4> QED BY <4>1, <3>pt
    <3> QED BY <3>pt, <3>a2, <3>b2
  <2> QED BY <2>a, <2>b
<1>ind. PrevTranAbsorbP(m)  BY <1>cl, TranExclusiveInduction
<1> QED BY <1>ind DEF PrevTranAbsorbP
====================================================================
