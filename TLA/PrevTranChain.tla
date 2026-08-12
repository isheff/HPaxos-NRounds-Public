--------------------------- MODULE PrevTranChain ---------------------------
\*   TranExclusiveInduction, PrevTranRec, DeepestKnownInv, PrevTranStruct,
\*   TranSubMessages -> cited lemmas
\*   TLAPS -> proof-only
EXTENDS RecursiveWellFormed, TranExclusiveInduction, PrevTranRec,
        DeepestKnownInv, PrevTranStruct, TranSubMessages
LOCAL INSTANCE TLAPS

\* Induction motive, module-level so TranExclusiveInduction can instantiate
\* it by name.
PrevTranChainP(z) ==
  \A y1, y2 \in PrevTran(z) : y1 \in Tran(y2) \/ y2 \in Tran(y1)

\* A prevtran chain is totally ordered by Tran: any two members are
\* comparable. (Key to catching forks: two incomparable same-signer
\* messages can never sit on one chain.)
LEMMA PrevTranChain ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         NEW m \in Messages
  PROVE \A y1, y2 \in PrevTran(m) : y1 \in Tran(y2) \/ y2 \in Tran(y1)
<1>cl. \A x \in Messages :
         (\A yy \in TranExclusive(x) : PrevTranChainP(yy)) => PrevTranChainP(x)
  <2> SUFFICES ASSUME NEW x \in Messages,
                      \A yy \in TranExclusive(x) : PrevTranChainP(yy)
      PROVE PrevTranChainP(x)
    OBVIOUS
  <2>rec. PrevTran(x) = {x} \cup (IF Sig(x) \in DOMAIN DeepestKnown(x)
                                    THEN PrevTran(DeepestKnown(x)[Sig(x)][2].id)
                                    ELSE {})
    BY PrevTranRec
  <2>selfT. x \in Tran(x)  BY DEF Tran
  <2>a. CASE Sig(x) \notin DOMAIN DeepestKnown(x)
    <3>1. PrevTran(x) = {x}  BY <2>rec, <2>a
    <3> QED BY <3>1, <2>selfT DEF PrevTranChainP
  <2>b. CASE Sig(x) \in DOMAIN DeepestKnown(x)
    <3> DEFINE z1 == DeepestKnown(x)[Sig(x)][2].id
    <3>inv. DeepestKnownInvariant(x)  BY DeepestKnownInv
    <3>z1. z1 \in TranExclusive(x)
      BY <3>inv, <2>b DEF DeepestKnownInvariant
    <3>z1M. z1 \in Messages  BY <3>z1, TranSubMessages DEF TranExclusive
    <3>ih. PrevTranChainP(z1)  BY <3>z1
    <3>pt. PrevTran(x) = {x} \cup PrevTran(z1)  BY <2>rec, <2>b
    <3>sub1. PrevTran(z1) \subseteq Tran(z1)  BY <3>z1M, PrevTranStruct
    <3>t1. Tran(z1) \subseteq Tran(x)
      <4>1. z1 \in Tran(x)  BY <3>z1 DEF TranExclusive
      <4> QED BY <4>1 DEF TranTrans
    <3>inx. \A y \in PrevTran(z1) : y \in Tran(x)  BY <3>sub1, <3>t1
    <3> SUFFICES ASSUME NEW y1 \in PrevTran(x), NEW y2 \in PrevTran(x)
        PROVE y1 \in Tran(y2) \/ y2 \in Tran(y1)
      BY DEF PrevTranChainP
    <3>aa. CASE y1 = x /\ y2 = x
      <4> QED BY <3>aa, <2>selfT
    <3>ab. CASE y1 = x /\ y2 \in PrevTran(z1)
      <4>1. y2 \in Tran(x)  BY <3>ab, <3>inx
      <4> QED BY <4>1, <3>ab
    <3>ba. CASE y1 \in PrevTran(z1) /\ y2 = x
      <4>1. y1 \in Tran(x)  BY <3>ba, <3>inx
      <4> QED BY <4>1, <3>ba
    <3>bb. CASE y1 \in PrevTran(z1) /\ y2 \in PrevTran(z1)
      <4> QED BY <3>bb, <3>ih DEF PrevTranChainP
    <3> QED BY <3>pt, <3>aa, <3>ab, <3>ba, <3>bb
  <2> QED BY <2>a, <2>b
<1>ind. PrevTranChainP(m)  BY <1>cl, TranExclusiveInduction
<1> QED BY <1>ind DEF PrevTranChainP
====================================================================
