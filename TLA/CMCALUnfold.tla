----------------------------- MODULE CMCALUnfold -----------------------------
\* NaturalsInduction supplies RecursiveFcnOfNat; TLAPS supplies Isa/Zenon.
EXTENDS MessageConcrete, NaturalsInduction
LOCAL INSTANCE TLAPS

LEMMA CMCALUnfold ==
  \A l \in Nat : CMCAL[l] = IF l = 0 THEN CMCLBase ELSE CMCLExt(CMCAL[l-1])
<1> DEFINE Def(g, j) == IF j = 0 THEN CMCLBase ELSE CMCLExt(g[j-1])
<1> DEFINE mcl[j \in Nat] == Def(mcl, j)
<1>m1. ASSUME NEW j \in Nat, NEW g, NEW h, \A i \in 0..(j-1) : g[i] = h[i]
       PROVE  Def(g, j) = Def(h, j)
  <2>1. CASE j = 0  BY <2>1
  <2>2. CASE j # 0
    <3>1. g[j-1] = h[j-1]  BY <1>m1, <2>2
    <3> QED BY <3>1, <2>2
  <2> QED BY <2>1, <2>2
<1> HIDE DEF Def
<1>m2. mcl = [j \in Nat |-> Def(mcl, j)]  BY <1>m1, RecursiveFcnOfNat, Isa
<1>m3. mcl = CMCAL  BY Zenon DEF CMCAL, Def
<1>4. CMCAL = [j \in Nat |-> Def(CMCAL, j)]  BY <1>m2, <1>m3
<1> QED BY <1>4 DEF Def
=============================================================================
