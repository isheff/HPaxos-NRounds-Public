------------------------- MODULE LevelIndepGFunMI -------------------------
\*   MessageInterface  -> Messages, Tran, MessagesWithTranSizeAtMost, GFunMI,
\*                        GRecMI (statement and proof)
\*   FiniteSetTheorems -> GeneralNatInduction (via WellFoundedInduction)
\*   gStepMI, TranCardNat -> cited lemmas. They share MessageInterface with
\*                        this module, so they must be EXTENDS: LOCAL INSTANCE
\*                        would copy that shared base and split the operators.
\*   TLAPS             -> IsaM, SMT; proof-only
EXTENDS MessageInterface, FiniteSetTheorems, gStepMI, TranCardNat
LOCAL INSTANCE TLAPS

\* Level-independence for an abstract g satisfying the recursion, by
\* course-of-values induction on the Cardinality(Tran(.)) measure.
LEMMA LevelIndepGFunMI ==
  ASSUME TranFinite,
         NEW F(_,_), NEW R(_),
         \A w \in Messages : R(w) \subseteq Messages,
         \A w \in Messages : \A y \in R(w) :
             Cardinality(Tran(y)) < Cardinality(Tran(w)),
         NEW ll \in Nat, NEW xx \in MessagesWithTranSizeAtMost(ll)
  PROVE  GFunMI(F, R)[ll][xx] = GFunMI(F, R)[Cardinality(Tran(xx))][xx]
<1> DEFINE g == GFunMI(F, R)
<1> DEFINE lev(z) == Cardinality(Tran(z))
<1>grec. GRecMI(g, F, R)  BY gStepMI DEF GRecMI
<1> DEFINE Q(n) == \A x \in MessagesWithTranSizeAtMost(n) : g[n][x] = g[lev(x)][x]
<1> SUFFICES \A n \in Nat : Q(n)  BY DEF Q
<1> HIDE DEF Q
<1>ind. \A n \in Nat : (\A mm \in 0..(n-1) : Q(mm)) => Q(n)
  <2> USE DEF Q
  <2> SUFFICES ASSUME NEW n \in Nat, \A mm \in 0..(n-1) : Q(mm),
                      NEW x \in MessagesWithTranSizeAtMost(n)
               PROVE  g[n][x] = g[lev(x)][x]
    OBVIOUS
  <2>mc. x \in Messages /\ lev(x) <= n  BY DEF MessagesWithTranSizeAtMost
  <2>lev. lev(x) \in Nat  BY <2>mc, TranCardNat
  <2>xl. x \in MessagesWithTranSizeAtMost(lev(x))  BY <2>mc, <2>lev DEF MessagesWithTranSizeAtMost
  <2>gn. g[n][x] = F(x, IF n = 0 THEN {} ELSE {g[n-1][y] : y \in R(x)})
    BY <1>grec DEF GRecMI
  <2>gl. g[lev(x)][x] = F(x, IF lev(x) = 0 THEN {} ELSE {g[lev(x)-1][y] : y \in R(x)})
    BY <2>lev, <2>xl, <1>grec DEF GRecMI
  <2> SUFFICES (IF n = 0 THEN {} ELSE {g[n-1][y] : y \in R(x)})
             = (IF lev(x) = 0 THEN {} ELSE {g[lev(x)-1][y] : y \in R(x)})
    BY <2>gn, <2>gl
  <2>R. \A y \in R(x) : y \in Messages /\ lev(y) \in Nat /\ lev(y) < lev(x)
    <3>1. ASSUME NEW y \in R(x)
          PROVE  y \in Messages /\ lev(y) \in Nat /\ lev(y) < lev(x)
      <4>1. y \in Messages   BY <2>mc
      <4>2. lev(y) \in Nat   BY <4>1, TranCardNat
      <4>3. lev(y) < lev(x)  BY <2>mc
      <4> QED BY <4>1, <4>2, <4>3
    <3> QED BY <3>1
  <2>1. CASE n = 0
    <3>1. lev(x) = 0   BY <2>1, <2>mc, <2>lev, SMT
    <3> QED BY <2>1, <3>1
  <2>2. CASE n # 0 /\ lev(x) = 0
    <3>1. R(x) = {}    BY <2>2, <2>R
    <3>2. {g[n-1][y] : y \in R(x)} = {}  BY <3>1
    <3> QED BY <2>2, <3>2
  <2>3. CASE n # 0 /\ lev(x) # 0
    <3>0. /\ n-1 \in Nat /\ lev(x)-1 \in Nat
          /\ n-1 \in 0..(n-1) /\ lev(x)-1 \in 0..(n-1)
      BY <2>3, <2>mc, <2>lev, SMT
    <3>1. {g[n-1][y] : y \in R(x)} = {g[lev(x)-1][y] : y \in R(x)}
      <4>1. ASSUME NEW y \in R(x) PROVE g[n-1][y] = g[lev(x)-1][y]
        <5>1. y \in Messages /\ lev(y) \in Nat /\ lev(y) < lev(x)   BY <2>R
        <5>3. lev(y) <= n-1 /\ lev(y) <= lev(x)-1     BY <5>1, <2>3, <2>mc, <2>lev, <3>0, SMT
        <5>4. y \in MessagesWithTranSizeAtMost(n-1)      BY <5>1, <5>3 DEF MessagesWithTranSizeAtMost
        <5>5. y \in MessagesWithTranSizeAtMost(lev(x)-1) BY <5>1, <5>3 DEF MessagesWithTranSizeAtMost
        <5>8. g[n-1][y] = g[lev(y)][y]                BY <3>0, <5>4
        <5>9. g[lev(x)-1][y] = g[lev(y)][y]           BY <3>0, <5>5
        <5> QED BY <5>8, <5>9
      <4> QED BY <4>1
    <3> QED BY <2>3, <3>1
  <2> QED BY <2>1, <2>2, <2>3
<1> QED BY <1>ind, GeneralNatInduction, IsaM("blast")
====================================================================
