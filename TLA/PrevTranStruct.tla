-------------------------- MODULE PrevTranStruct --------------------------
\*   TranExclusiveInduction, PrevTranRec, DeepestKnownInv, TranSubMessages
\*     -> cited lemmas
\*   TLAPS -> proof-only
EXTENDS RecursiveWellFormed, TranExclusiveInduction, PrevTranRec,
        DeepestKnownInv, TranSubMessages
LOCAL INSTANCE TLAPS

\* Induction motive, module-level so TranExclusiveInduction can instantiate
\* it by name.
PrevTranStructP(z) ==
  /\ z \in PrevTran(z)
  /\ PrevTran(z) \subseteq Tran(z)
  /\ \A y \in PrevTran(z) : Sig(y) = Sig(z)

\* Basic chain structure: PrevTran(z) contains z, stays inside Tran(z), and
\* consists solely of messages signed by Sig(z).
LEMMA PrevTranStruct ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         NEW m \in Messages
  PROVE /\ m \in PrevTran(m)
        /\ PrevTran(m) \subseteq Tran(m)
        /\ \A y \in PrevTran(m) : Sig(y) = Sig(m)
<1>cl. \A x \in Messages :
         (\A yy \in TranExclusive(x) : PrevTranStructP(yy)) => PrevTranStructP(x)
  <2> SUFFICES ASSUME NEW x \in Messages,
                      \A yy \in TranExclusive(x) : PrevTranStructP(yy)
      PROVE PrevTranStructP(x)
    OBVIOUS
  <2>rec. PrevTran(x) = {x} \cup (IF Sig(x) \in DOMAIN DeepestKnown(x)
                                    THEN PrevTran(DeepestKnown(x)[Sig(x)][2].id)
                                    ELSE {})
    BY PrevTranRec
  <2>a. CASE Sig(x) \notin DOMAIN DeepestKnown(x)
    <3>1. PrevTran(x) = {x}  BY <2>rec, <2>a
    <3>2. x \in Tran(x)  BY DEF Tran
    <3> QED BY <3>1, <3>2 DEF PrevTranStructP
  <2>b. CASE Sig(x) \in DOMAIN DeepestKnown(x)
    <3> DEFINE z1 == DeepestKnown(x)[Sig(x)][2].id
    <3>inv. DeepestKnownInvariant(x)  BY DeepestKnownInv
    <3>z1. z1 \in TranExclusive(x) /\ Sig(z1) = Sig(x)
      BY <3>inv, <2>b DEF DeepestKnownInvariant
    <3>ih. PrevTranStructP(z1)  BY <3>z1
    <3>pt. PrevTran(x) = {x} \cup PrevTran(z1)  BY <2>rec, <2>b
    <3>t1. Tran(z1) \subseteq Tran(x)
      <4>1. z1 \in Tran(x)  BY <3>z1 DEF TranExclusive
      <4> QED BY <4>1 DEF TranTrans
    <3>selfx. x \in PrevTran(x)  BY <3>pt
    <3>sub. PrevTran(x) \subseteq Tran(x)
      <4>1. PrevTran(z1) \subseteq Tran(z1)  BY <3>ih DEF PrevTranStructP
      <4>2. x \in Tran(x)  BY DEF Tran
      <4> QED BY <3>pt, <4>1, <3>t1, <4>2
    <3>sig. \A y \in PrevTran(x) : Sig(y) = Sig(x)
      <4>1. \A y \in PrevTran(z1) : Sig(y) = Sig(z1)  BY <3>ih DEF PrevTranStructP
      <4> QED BY <3>pt, <4>1, <3>z1
    <3> QED BY <3>selfx, <3>sub, <3>sig DEF PrevTranStructP
  <2> QED BY <2>a, <2>b
<1>ind. PrevTranStructP(m)  BY <1>cl, TranExclusiveInduction
<1> QED BY <1>ind DEF PrevTranStructP
====================================================================
