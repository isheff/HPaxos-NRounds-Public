----------------------------- MODULE gStepMI -----------------------------
\*   MessageInterface  -> MessagesWithTranSizeAtMost, GFunMI (statement)
\*   NaturalsInduction -> RecursiveFcnOfNat (proof)
\*   TLAPS             -> Isa, Zenon; proof-only, no colliding operators
EXTENDS MessageInterface, NaturalsInduction
LOCAL INSTANCE TLAPS

\* The defining equation of GFunMI's inner recursive function, from
\* RecursiveFcnOfNat (the body at level l uses only level l-1).
LEMMA gStepMI ==
  ASSUME NEW F(_,_), NEW R(_), NEW l \in Nat,
         NEW x \in MessagesWithTranSizeAtMost(l)
  PROVE  GFunMI(F, R)[l][x] =
           F(x, IF l = 0 THEN {} ELSE {GFunMI(F, R)[l-1][y] : y \in R(x)})
<1> DEFINE Def(g, k) == [z \in MessagesWithTranSizeAtMost(k) |->
                          F(z, IF k = 0 THEN {} ELSE {g[k-1][w] : w \in R(z)})]
<1> DEFINE gg[k \in Nat] == Def(gg, k)
<1>1. ASSUME NEW k \in Nat, NEW g, NEW h, \A i \in 0..(k-1) : g[i] = h[i]
      PROVE  Def(g, k) = Def(h, k)
  BY <1>1
<1> HIDE DEF Def
<1>2. gg = [k \in Nat |-> Def(gg, k)]  BY <1>1, RecursiveFcnOfNat, Isa
<1>3. gg = GFunMI(F, R)  BY Zenon DEF GFunMI, Def
<1>4. GFunMI(F, R) = [k \in Nat |-> Def(GFunMI(F, R), k)]  BY <1>2, <1>3
<1>5. GFunMI(F, R)[l] = Def(GFunMI(F, R), l)  BY <1>4
<1> QED  BY <1>5 DEF Def
====================================================================
