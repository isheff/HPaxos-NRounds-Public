---------------------------- MODULE CLevelIndepGen ----------------------------
EXTENDS MessageConcrete, CMinLevelDom, CMCALMonoMem, NaturalsInduction
LOCAL INSTANCE TLAPS

LEMMA CLevelIndepGen ==
  ASSUME NEW g, NEW F(_,_), NEW R(_),
         CGRec(g, F, R),
         \A w \in CMC : R(w) \subseteq CMC,
         \A w \in CMC : \A y \in R(w) :
             CMinLevel(y) < CMinLevel(w),
         NEW ll \in Nat, NEW xx \in CMCAL[ll]
  PROVE  g[ll][xx] = g[CMinLevel(xx)][xx]
<1> DEFINE lev(z) == CMinLevel(z)
<1> DEFINE Q(n) == CQPred(g, n)
<1> SUFFICES \A n \in Nat : Q(n)
  BY DEF Q, CQPred
<1> HIDE DEF Q
<1>ind. \A n \in Nat : (\A mm \in 0..(n-1) : Q(mm)) => Q(n)
  <2> USE DEF Q, CQPred
  <2> SUFFICES ASSUME NEW n \in Nat, \A mm \in 0..(n-1) : Q(mm)
               PROVE  Q(n)
    OBVIOUS
  <2> SUFFICES ASSUME NEW x \in CMCAL[n]
               PROVE  g[n][x] = g[lev(x)][x]
    OBVIOUS
  <2>mc. x \in CMC  BY DEF CMC
  <2>lev. lev(x) \in Nat /\ x \in CMCAL[lev(x)] /\ lev(x) <= n
    BY <2>mc, CMinLevelDom
  <2>gn. g[n][x] = F(x, IF n = 0 THEN {} ELSE {g[n-1][y] : y \in R(x)})
    BY DEF CGRec
  <2>gl. g[lev(x)][x] = F(x, IF lev(x) = 0 THEN {} ELSE {g[lev(x)-1][y] : y \in R(x)})
    BY <2>lev DEF CGRec
  <2> SUFFICES (IF n = 0 THEN {} ELSE {g[n-1][y] : y \in R(x)})
             = (IF lev(x) = 0 THEN {} ELSE {g[lev(x)-1][y] : y \in R(x)})
    BY <2>gn, <2>gl
  <2>R. \A y \in R(x) : y \in CMC /\ lev(y) \in Nat /\ lev(y) < lev(x)
    <3>1. ASSUME NEW y \in R(x)
          PROVE  y \in CMC /\ lev(y) \in Nat /\ lev(y) < lev(x)
      <4>1. y \in CMC   BY <2>mc
      <4>2. lev(y) \in Nat           BY <4>1, CMinLevelDom
      <4>3. lev(y) < lev(x)          BY <2>mc
      <4> QED BY <4>1, <4>2, <4>3
    <3> QED BY <3>1
  <2>1. CASE n = 0
    <3>1. lev(x) = 0   BY <2>1, <2>lev
    <3> QED BY <2>1, <3>1
  <2>2. CASE n # 0 /\ lev(x) = 0
    <3>1. R(x) = {}    BY <2>2, <2>R
    <3> QED BY <2>2, <3>1
  <2>3. CASE n # 0 /\ lev(x) # 0
    <3>0. /\ n-1 \in Nat /\ lev(x)-1 \in Nat
          /\ n-1 \in 0..(n-1) /\ lev(x)-1 \in 0..(n-1)
      BY <2>3, <2>lev
    <3>1. {g[n-1][y] : y \in R(x)} = {g[lev(x)-1][y] : y \in R(x)}
      <4>1. ASSUME NEW y \in R(x) PROVE g[n-1][y] = g[lev(x)-1][y]
        <5>1. y \in CMC /\ lev(y) \in Nat /\ lev(y) < lev(x)   BY <2>R
        <5>2. y \in CMCAL[lev(y)]   BY <5>1, CMinLevelDom
        <5>3. lev(y) <= n-1 /\ lev(y) <= lev(x)-1     BY <5>1, <2>3, <2>lev, <3>0
        <5>4. y \in CMCAL[n-1]      BY <5>1, <5>2, <5>3, <3>0, CMCALMonoMem
        <5>5. y \in CMCAL[lev(x)-1] BY <5>1, <5>2, <5>3, <3>0, CMCALMonoMem
        <5>8. g[n-1][y] = g[lev(y)][y]                BY <3>0, <5>4
        <5>9. g[lev(x)-1][y] = g[lev(y)][y]           BY <3>0, <5>5
        <5> QED BY <5>8, <5>9
      <4> QED BY <4>1
    <3> QED BY <2>3, <3>1
  <2> QED BY <2>1, <2>2, <2>3
<1> QED BY <1>ind, GeneralNatInduction, IsaM("blast")
=============================================================================
