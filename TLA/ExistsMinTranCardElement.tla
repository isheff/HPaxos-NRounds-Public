--------------------- MODULE ExistsMinTranCardElement ---------------------
\*   FiniteSetTheorems -> GeneralNatInduction
\*   TranCardNat       -> cited lemma
\*   TLAPS             -> IsaM; proof-only
\* TranCard is one of the definitions kept in MessageInterface precisely so
\* it can be used by name here rather than as an anonymous lambda.
EXTENDS MessageInterface, FiniteSetTheorems, TranCardNat
LOCAL INSTANCE TLAPS

\* Generic min-existence for Cardinality(Tran(.)) over a possibly-unbounded
\* message set (Nat well-ordering, no finiteness of S needed).
LEMMA ExistsMinTranCardElement ==
  ASSUME TranFinite,
         NEW S \in SUBSET Messages, S # {}
  PROVE \E x \in S : \A y \in S : TranCard(x) <= TranCard(y)
<1> DEFINE Q(n) == \A T \in SUBSET Messages : (\E t \in T : TranCard(t) = n)
                     => (\E x \in T : \A y \in T : TranCard(x) <= TranCard(y))
<1> SUFFICES \A n \in Nat : Q(n)
  <2>1. PICK s0 \in S : TRUE  OBVIOUS
  <2>2. s0 \in Messages  BY <2>1
  <2>3. TranCard(s0) \in Nat  BY <2>2, TranCardNat DEF TranCard
  <2>5. \E t \in S : TranCard(t) = TranCard(s0)  BY <2>1
  <2> QED BY <2>3, <2>5 DEF Q
<1> HIDE DEF Q
<1>ind. \A n \in Nat : (\A k \in 0..(n-1) : Q(k)) => Q(n)
  <2> USE DEF Q
  <2> SUFFICES ASSUME NEW n \in Nat, \A k \in 0..(n-1) : Q(k),
                      NEW T \in SUBSET Messages, NEW t \in T, TranCard(t) = n
               PROVE \E x \in T : \A y \in T : TranCard(x) <= TranCard(y)
    OBVIOUS
  <2> DEFINE T2 == {y \in T : TranCard(y) < n}
  <2>1. CASE T2 = {}
    <3>1. \A y \in T : TranCard(y) >= n
      <4> SUFFICES ASSUME NEW y \in T PROVE TranCard(y) >= n  OBVIOUS
      <4>yM. y \in Messages  OBVIOUS
      <4>yNat. TranCard(y) \in Nat  BY <4>yM, TranCardNat DEF TranCard
      <4> QED BY <2>1, <4>yNat
    <3> QED BY <3>1
  <2>2. CASE T2 # {}
    <3>t2. PICK t2 \in T2 : TRUE  BY <2>2
    <3>t2T. t2 \in T /\ TranCard(t2) < n  BY <3>t2
    <3>t2M. t2 \in Messages  BY <3>t2T
    <3>t2Nat. TranCard(t2) \in Nat  BY <3>t2M, TranCardNat DEF TranCard
    <3>k. TranCard(t2) \in 0..(n-1)  BY <3>t2T, <3>t2Nat
    <3>Qk. \A k \in 0..(n-1) : Q(k)  OBVIOUS
    <3>Qbt2. Q(TranCard(t2))  BY <3>k, <3>Qk
    <3>wit. \E tt \in T : TranCard(tt) = TranCard(t2)  BY <3>t2T
    <3> QED BY <3>Qbt2, <3>wit DEF Q
  <2> QED BY <2>1, <2>2
<1> QED BY <1>ind, GeneralNatInduction, IsaM("blast")
====================================================================
