-------------------------- MODULE CRecursiveFuncRec --------------------------
EXTENDS MessageConcrete, CMinLevelDom, CMCALMonoMem, CRMFViaG, CGStep, CLevelIndep

LEMMA CRecursiveFuncRec ==
  ASSUME NEW F(_,_),
         NEW R(_),
         NEW m \in CMC,
         \A x \in CMC : R(x) \subseteq CMC,
         \A x \in CMC : \A y \in R(x) :
             CMinLevel(y) < CMinLevel(x)
  PROVE CRecursiveFunc(F, R, m) =
    F(m, {CRecursiveFunc(F, R, p): p \in R(m)})
<1> DEFINE g == CGFun(F, R)
<1> DEFINE lev(z) == CMinLevel(z)
<1>dom. lev(m) \in Nat /\ m \in CMCAL[lev(m)]
  BY CMinLevelDom
<1>sub. ASSUME NEW p \in R(m)
        PROVE  /\ p \in CMC
               /\ lev(p) \in Nat
               /\ lev(p) < lev(m)
  <2>1. p \in CMC  BY <1>dom
  <2>2. lev(p) \in Nat          BY <2>1, CMinLevelDom
  <2>3. lev(p) < lev(m)         BY <1>dom, <2>1
  <2> QED BY <2>1, <2>2, <2>3
<1>1. CRecursiveFunc(F, R, m) = g[lev(m)][m]
  BY CRMFViaG
<1>2. g[lev(m)][m] = F(m, IF lev(m) = 0 THEN {} ELSE {g[lev(m)-1][y] : y \in R(m)})
  BY <1>dom, CGStep
<1> SUFFICES (IF lev(m) = 0 THEN {} ELSE {g[lev(m)-1][y] : y \in R(m)})
             = {CRecursiveFunc(F, R, p) : p \in R(m)}
  BY <1>1, <1>2
<1>3. CASE lev(m) = 0
  <2>1. R(m) = {}
    BY <1>3, <1>sub
  <2> QED BY <1>3, <2>1
<1>4. CASE lev(m) # 0
  <2>0. lev(m) - 1 \in Nat /\ lev(m) - 1 < lev(m)  BY <1>dom, <1>4
  <2>1. {g[lev(m)-1][y] : y \in R(m)} = {CRecursiveFunc(F, R, p) : p \in R(m)}
    <3>1. ASSUME NEW y \in R(m)
          PROVE  g[lev(m)-1][y] = CRecursiveFunc(F, R, y)
      <4>1. y \in CMC /\ lev(y) \in Nat /\ lev(y) < lev(m)  BY <1>sub
      <4>2. y \in CMCAL[lev(y)]                        BY <4>1, CMinLevelDom
      <4>3. lev(y) <= lev(m) - 1                                         BY <4>1, <2>0, <1>dom
      <4>4. y \in CMCAL[lev(m)-1]
        BY <4>1, <4>2, <4>3, <2>0, CMCALMonoMem
      <4>5. g[lev(m)-1][y] = g[lev(y)][y]                                BY <2>0, <4>4, CLevelIndep
      <4>6. CRecursiveFunc(F, R, y) = g[lev(y)][y]                 BY CRMFViaG
      <4> QED BY <4>5, <4>6
    <3> QED BY <3>1
  <2> QED BY <1>4, <2>1
<1> QED BY <1>3, <1>4
=============================================================================
