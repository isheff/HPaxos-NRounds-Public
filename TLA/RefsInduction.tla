-------------------------- MODULE RefsInduction --------------------------
\*   FiniteSetTheorems -> GeneralNatInduction
\*   TranCardNat, TranSubMessages, TranExclusiveDecreasesTranSize -> cited
\*   TLAPS             -> IsaM; proof-only
EXTENDS MessageInterface, FiniteSetTheorems,
        TranCardNat, TranSubMessages, TranExclusiveDecreasesTranSize
LOCAL INSTANCE TLAPS

\* Well-founded induction along Refs.  Course-of-values on Cardinality(Tran(.))
\* (this file's level measure): a message x's refs have strictly smaller Tran
\* (TranExclusiveDecreasesTranSize, via Refs(x) \subseteq TranExclusive(x)) and
\* stay within Messages (TranSubMessages), so each ref satisfies H by the IH;
\* the hypothesis then lifts that to H(x). Mirrors HPaxos.tla's RefsInduction.
THEOREM RefsInduction ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         NEW m \in Messages,
         NEW H(_),
         \A x \in Messages: (\A y \in Refs(x) : H(y)) => H(x)
  PROVE H(m)
<1> DEFINE lev(z) == Cardinality(Tran(z))
<1> DEFINE Q(n) == \A x \in Messages : lev(x) = n => H(x)
<1> SUFFICES \A n \in Nat : Q(n)  BY TranCardNat DEF Q
<1> HIDE DEF Q
<1>ind. \A n \in Nat : (\A kk \in 0..(n-1) : Q(kk)) => Q(n)
  <2> USE DEF Q
  <2> SUFFICES ASSUME NEW n \in Nat, \A kk \in 0..(n-1) : Q(kk),
                      NEW x \in Messages, lev(x) = n
               PROVE  H(x)
    OBVIOUS
  <2>sub. Refs(x) \subseteq TranExclusive(x)  BY DEF Refs
  <2>tc. Refs(x) \subseteq Messages  BY <2>sub, TranSubMessages DEF TranExclusive
  <2>r. \A y \in Refs(x) : H(y)
    <3> SUFFICES ASSUME NEW y \in Refs(x) PROVE H(y)  OBVIOUS
    <3>3. y \in Messages  BY <2>tc
    <3>5. lev(y) < lev(x)  BY <2>sub, TranExclusiveDecreasesTranSize
    <3>6. lev(y) \in Nat  BY <3>3, TranCardNat
    <3>7. lev(y) \in 0..(n-1)  BY <3>5, <3>6
    <3> QED BY <3>3, <3>7
  <2> QED BY <2>r
<1> QED BY <1>ind, GeneralNatInduction, IsaM("blast")
====================================================================
