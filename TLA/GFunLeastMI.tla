--------------------------- MODULE GFunLeastMI ---------------------------
\*   FiniteSetTheorems -> GeneralNatInduction (via WellFoundedInduction)
\*   TranCardNat, GFunRecMI -> cited lemmas
\*   TLAPS             -> IsaM, SMT; proof-only
EXTENDS MessageInterface, FiniteSetTheorems, TranCardNat, GFunRecMI
LOCAL INSTANCE TLAPS

\* Any solution H of the recursion equals the canonical GFunMI solution,
\* by course-of-values induction on the Cardinality(Tran(.)) measure.
LEMMA GFunLeastMI ==
  ASSUME TranFinite, NEW F(_,_), NEW R(_), NEW H(_),
         \A x \in Messages : R(x) \subseteq Messages,
         \A x \in Messages : \A y \in R(x) :
             Cardinality(Tran(y)) < Cardinality(Tran(x)),
         \A mm \in Messages : H(mm) = F(mm, {H(p) : p \in R(mm)})
  PROVE \A mm \in Messages : H(mm) = GFunMI(F, R)[Cardinality(Tran(mm))][mm]
<1> DEFINE lev(z) == Cardinality(Tran(z))
<1> DEFINE Q(n) == \A mm \in Messages : lev(mm) = n =>
                     H(mm) = GFunMI(F, R)[lev(mm)][mm]
<1> SUFFICES \A n \in Nat : Q(n)  BY TranCardNat DEF Q
<1> HIDE DEF Q
<1>ind. \A n \in Nat : (\A kk \in 0..(n-1) : Q(kk)) => Q(n)
  <2> USE DEF Q
  <2> SUFFICES ASSUME NEW n \in Nat, \A kk \in 0..(n-1) : Q(kk),
                      NEW mm \in Messages, lev(mm) = n
               PROVE  H(mm) = GFunMI(F, R)[lev(mm)][mm]
    OBVIOUS
  <2>1. H(mm) = F(mm, {H(p) : p \in R(mm)})  OBVIOUS
  <2>2. GFunMI(F, R)[lev(mm)][mm] = F(mm, {GFunMI(F, R)[lev(p)][p] : p \in R(mm)})
    BY GFunRecMI
  <2>3. {H(p) : p \in R(mm)} = {GFunMI(F, R)[lev(p)][p] : p \in R(mm)}
    <3>1. ASSUME NEW p \in R(mm) PROVE H(p) = GFunMI(F, R)[lev(p)][p]
      <4>1. p \in Messages  OBVIOUS
      <4>2. lev(p) < lev(mm)  OBVIOUS
      <4>3. lev(p) \in Nat  BY <4>1, TranCardNat
      <4>4. lev(p) \in 0..(n-1)  BY <4>2, <4>3, SMT
      <4> QED BY <4>1, <4>4
    <3> QED BY <3>1
  <2> QED BY <2>1, <2>2, <2>3
<1> QED BY <1>ind, GeneralNatInduction, IsaM("blast")
====================================================================
