----------------- MODULE CombinedFreshQdLrnsIdUnique -----------------
\*   FiniteSetTheorems -> GeneralNatInduction
\*   TranCardNat, CombinedFreshQdLrnsIdRec, TranSubMessages,
\*   TranExclusiveDecreasesTranSize -> cited lemmas
\*   TLAPS -> IsaM, SMT; proof-only
EXTENDS MessageInterface, FiniteSetTheorems,
        TranCardNat, CombinedFreshQdLrnsIdRec,
        TranSubMessages, TranExclusiveDecreasesTranSize
LOCAL INSTANCE TLAPS

\* CombinedFreshQdLrnsId is the UNIQUE solution of its recursion, via
\* "any two solutions of the same recursion agree" specialized to
\* F := CombinedFreshQdLrnsIdR.
THEOREM CombinedFreshQdLrnsIdUnique ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic, NEW H(_),
         \A x \in Messages :
            H(x) = CombinedFreshQdLrnsIdR(x, {H(p) : p \in TranExclusive(x)})
  PROVE \A x \in Messages : H(x) = CombinedFreshQdLrnsId(x)
<1> DEFINE lev(z) == Cardinality(Tran(z))
<1> DEFINE Q(n) == \A mm \in Messages : lev(mm) = n =>
                     H(mm) = CombinedFreshQdLrnsId(mm)
<1> SUFFICES \A n \in Nat : Q(n)  BY TranCardNat DEF Q
<1> HIDE DEF Q
<1>ind. \A n \in Nat : (\A kk \in 0..(n-1) : Q(kk)) => Q(n)
  <2> USE DEF Q
  <2> SUFFICES ASSUME NEW n \in Nat, \A kk \in 0..(n-1) : Q(kk),
                      NEW mm \in Messages, lev(mm) = n
               PROVE  H(mm) = CombinedFreshQdLrnsId(mm)
    OBVIOUS
  <2>1. H(mm) = CombinedFreshQdLrnsIdR(mm, {H(p) : p \in TranExclusive(mm)})  OBVIOUS
  <2>2. CombinedFreshQdLrnsId(mm)
          = CombinedFreshQdLrnsIdR(mm, {CombinedFreshQdLrnsId(p) : p \in TranExclusive(mm)})
    BY CombinedFreshQdLrnsIdRec
  <2>3. {H(p) : p \in TranExclusive(mm)} = {CombinedFreshQdLrnsId(p) : p \in TranExclusive(mm)}
    <3>1. ASSUME NEW p \in TranExclusive(mm) PROVE H(p) = CombinedFreshQdLrnsId(p)
      <4>1. p \in Messages  BY TranSubMessages DEF TranExclusive
      <4>2. lev(p) < lev(mm)  BY TranExclusiveDecreasesTranSize
      <4>3. lev(p) \in Nat  BY <4>1, TranCardNat
      <4>4. lev(p) \in 0..(n-1)  BY <4>2, <4>3, SMT
      <4> QED BY <4>1, <4>4
    <3> QED BY <3>1
  <2> QED BY <2>1, <2>2, <2>3
<1> QED BY <1>ind, GeneralNatInduction, IsaM("blast")
====================================================================
