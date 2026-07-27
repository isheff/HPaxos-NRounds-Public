---------------------------- MODULE GFunRecMI ----------------------------
\*   MessageInterface     -> Messages, Tran, MessagesWithTranSizeAtMost, GFunMI
\*   FiniteSetTheorems    -> FS_EmptySet (proof)
\*   gStepMI, TranCardNat, LevelIndepGFunMI -> cited lemmas, all sharing
\*                           MessageInterface with this module, hence EXTENDS
\*   TLAPS                -> SMT; proof-only
EXTENDS MessageInterface, FiniteSetTheorems,
        gStepMI, TranCardNat, LevelIndepGFunMI
LOCAL INSTANCE TLAPS

\* The recursion equation for GFunMI evaluated at a message's own level.
LEMMA GFunRecMI ==
  ASSUME TranFinite, NEW F(_,_), NEW R(_), NEW m \in Messages,
         \A x \in Messages : R(x) \subseteq Messages,
         \A x \in Messages : \A y \in R(x) :
             Cardinality(Tran(y)) < Cardinality(Tran(x))
  PROVE GFunMI(F, R)[Cardinality(Tran(m))][m]
        = F(m, {GFunMI(F, R)[Cardinality(Tran(x))][x] : x \in R(m)})
<1> DEFINE M == Cardinality(Tran(m))
<1>fin. IsFiniteSet(Tran(m)) /\ M \in Nat  BY TranCardNat
<1>mm. m \in MessagesWithTranSizeAtMost(M)
  <2>1. Cardinality(Tran(m)) \in Nat  BY TranCardNat
  <2>2. Cardinality(Tran(m)) <= M  BY <2>1, <1>fin, SMT
  <2> QED BY <2>2 DEF MessagesWithTranSizeAtMost
<1>nz. M # 0
  <2>1. m \in Tran(m)  BY DEF Tran
  <2> QED BY <1>fin, <2>1, FS_EmptySet
<1>step. GFunMI(F, R)[M][m]
           = F(m, IF M = 0 THEN {} ELSE {GFunMI(F, R)[M-1][y] : y \in R(m)})
  BY <1>fin, <1>mm, gStepMI
<1>unfold. GFunMI(F, R)[M][m] = F(m, {GFunMI(F, R)[M-1][y] : y \in R(m)})
  BY <1>step, <1>nz
<1>eq. {GFunMI(F, R)[M-1][y] : y \in R(m)}
       = {GFunMI(F, R)[Cardinality(Tran(x))][x] : x \in R(m)}
  <2>0. M - 1 \in Nat  BY <1>fin, <1>nz, SMT
  <2>1. ASSUME NEW y \in R(m)
        PROVE GFunMI(F, R)[M-1][y] = GFunMI(F, R)[Cardinality(Tran(y))][y]
    <3>1. y \in Messages  OBVIOUS
    <3>2. Cardinality(Tran(y)) < M  OBVIOUS
    <3>3. Cardinality(Tran(y)) \in Nat  BY <3>1, TranCardNat
    <3>4. Cardinality(Tran(y)) <= M-1  BY <3>2, <3>3, <2>0, <1>fin, SMT
    <3>5. y \in MessagesWithTranSizeAtMost(M-1)  BY <3>1, <3>4 DEF MessagesWithTranSizeAtMost
    <3> QED BY <2>0, <3>5, LevelIndepGFunMI
  <2> QED BY <2>1
<1> QED BY <1>unfold, <1>eq
====================================================================
