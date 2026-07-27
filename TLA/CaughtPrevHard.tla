-------------------------- MODULE CaughtPrevHard --------------------------
\*   FiniteSetTheorems -> GeneralNatInduction
\*   TranCardNat, TranExclusiveDecreasesTranSize, PrevDom,
\*   PrevComparableEqual, TranAntisym -> cited lemmas
\*   TLAPS -> IsaM; proof-only
EXTENDS MessageInterface, FiniteSetTheorems,
        TranCardNat, TranExclusiveDecreasesTranSize,
        PrevDom, PrevComparableEqual, TranAntisym
LOCAL INSTANCE TLAPS

\* Hard direction: any incomparable same-sig pair in a transitively-closed m
\* reduces, by strong induction on the summed Tran-size measure, to a pair
\* satisfying the (both empty) \/ (intersection) target.
LEMMA CaughtPrevHard ==
  ASSUME TypeOKMessageInterface, TranFinite, TranTrans, TranAcyclic,
         NEW m \in SUBSET Messages, \A xx \in m: TranExclusive(xx) \subseteq m,
         NEW a \in Acceptors, NEW pp1 \in m, NEW pp2 \in m,
         Sig(pp1) = a, Sig(pp2) = a, pp1 \notin Tran(pp2), pp2 \notin Tran(pp1)
  PROVE \E q1 \in m: \E q2 \in m: Sig(q1) = a /\ Sig(q2) = a /\ q1 # q2 /\
          ((Prev(q1) = {} /\ Prev(q2) = {}) \/ (Prev(q1) \cap Prev(q2) # {}))
<1> DEFINE lev(z) == Cardinality(Tran(z))
<1> DEFINE Fork == \E q1 \in m: \E q2 \in m: Sig(q1)=a /\ Sig(q2)=a /\ q1 # q2 /\
          ((Prev(q1) = {} /\ Prev(q2) = {}) \/ (Prev(q1) \cap Prev(q2) # {}))
<1> DEFINE IncPair(z1,z2) == /\ z1 \in m /\ z2 \in m /\ Sig(z1)=a /\ Sig(z2)=a
                            /\ z1 \notin Tran(z2) /\ z2 \notin Tran(z1)
<1> DEFINE Q(n) == \A z1, z2 : (IncPair(z1,z2) /\ lev(z1)+lev(z2) = n) => Fork
<1>mM. m \subseteq Messages  OBVIOUS
<1>levfacts. \A z \in m : z \in Messages /\ lev(z) \in Nat
  <2> SUFFICES ASSUME NEW z \in m PROVE z \in Messages /\ lev(z) \in Nat  OBVIOUS
  <2>1. z \in Messages  BY <1>mM
  <2> QED BY <2>1, TranCardNat
<1> SUFFICES \A n \in Nat : Q(n)
  <2>1. IncPair(pp1, pp2)  BY DEF IncPair
  <2>2. lev(pp1) + lev(pp2) \in Nat  BY <1>levfacts
  <2> QED BY <2>1, <2>2
<1> HIDE DEF Q
<1>ind. \A n \in Nat : (\A k \in 0..(n-1) : Q(k)) => Q(n)
  <2> USE DEF Q, IncPair, Fork
  <2> SUFFICES ASSUME NEW n \in Nat, \A k \in 0..(n-1) : Q(k),
                      NEW x1, NEW x2, IncPair(x1,x2), lev(x1)+lev(x2) = n
               PROVE  Fork
    OBVIOUS
  <2>x. x1 \in m /\ x2 \in m /\ Sig(x1) = a /\ Sig(x2) = a
        /\ x1 \notin Tran(x2) /\ x2 \notin Tran(x1)  OBVIOUS
  <2>mc. x1 \in Messages /\ x2 \in Messages  BY <2>x, <1>levfacts
  <2>lev. lev(x1) \in Nat /\ lev(x2) \in Nat  BY <2>x, <1>levfacts
  <2>ne. x1 # x2  BY <2>x DEF Tran
  <2>base. CASE Prev(x1) = {} /\ Prev(x2) = {}  BY <2>x, <2>ne, <2>base
  <2>nb. CASE ~(Prev(x1) = {} /\ Prev(x2) = {})
    <3>a. CASE Prev(x1) # {}
      <4>1. PICK q1 \in Prev(x1) : TRUE  BY <3>a
      <4>2. q1 \in TranExclusive(x1) /\ Sig(q1) = a  BY <4>1, <2>x DEF Prev
      <4>3. q1 \in Tran(x1) /\ q1 # x1  BY <4>2 DEF TranExclusive
      <4>4. q1 \in m
        <5>1. TranExclusive(x1) \subseteq m  BY <2>x
        <5> QED BY <4>2, <5>1
      <4>mc. q1 \in Messages /\ lev(q1) \in Nat  BY <4>4, <1>levfacts
      <4>5. lev(q1) < lev(x1)  BY <2>mc, <4>2, TranExclusiveDecreasesTranSize
      <4>6. x2 \notin Tran(q1)
        <5> SUFFICES ASSUME x2 \in Tran(q1) PROVE FALSE  OBVIOUS
        <5>1. Tran(q1) \subseteq Tran(x1)  BY <4>3, <2>mc, TranTrans DEF TranTrans
        <5> QED BY <5>1, <2>x
      <4>7. CASE q1 \notin Tran(x2)
        <5>1. IncPair(q1, x2)  BY <4>2, <4>4, <4>6, <4>7, <2>x
        <5>2. lev(q1) + lev(x2) \in 0..(n-1)  BY <4>5, <4>mc, <2>lev
        <5>3. Q(lev(q1) + lev(x2))  BY <5>2
        <5> QED BY <5>1, <5>3
      <4>8. CASE q1 \in Tran(x2)
        <5>1. q1 # x2  BY <4>3, <2>x
        <5>2. q1 \in TranExclusive(x2)  BY <4>8, <5>1 DEF TranExclusive
        <5>3. PICK r \in Prev(x2) : q1 \in Tran(r)  BY <5>2, <4>2, <2>mc, PrevDom
        <5>4. r \in TranExclusive(x2) /\ Sig(r) = a  BY <5>3, <2>x DEF Prev
        <5>5. r \in Tran(x2) /\ r # x2  BY <5>4 DEF TranExclusive
        <5>6. r \in m
          <6>1. TranExclusive(x2) \subseteq m  BY <2>x
          <6> QED BY <5>4, <6>1
        <5>mc. r \in Messages /\ lev(r) \in Nat  BY <5>6, <1>levfacts
        <5>7. lev(r) < lev(x2)  BY <2>mc, <5>4, TranExclusiveDecreasesTranSize
        <5>8. x1 \notin Tran(r)
          <6> SUFFICES ASSUME x1 \in Tran(r) PROVE FALSE  OBVIOUS
          <6>1. Tran(r) \subseteq Tran(x2)  BY <5>5, <2>mc, TranTrans DEF TranTrans
          <6> QED BY <6>1, <2>x
        <5>9. CASE r \notin Tran(x1)
          <6>1. IncPair(x1, r)  BY <5>4, <5>6, <5>8, <5>9, <2>x
          <6>2. lev(x1) + lev(r) \in 0..(n-1)  BY <5>7, <5>mc, <2>lev
          <6>3. Q(lev(x1) + lev(r))  BY <6>2
          <6> QED BY <6>1, <6>3
        <5>10. CASE r \in Tran(x1)
          <6>1. r \in TranExclusive(x1)  BY <5>5, <5>10, <2>x DEF TranExclusive
          <6>2. Sig(r) = Sig(x1)  BY <5>4, <2>x
          <6>3. PICK s \in Prev(x1) : r \in Tran(s)  BY <6>1, <6>2, <2>mc, PrevDom
          <6>sm. s \in m
            <7>1. s \in TranExclusive(x1)  BY <6>3 DEF Prev
            <7>2. TranExclusive(x1) \subseteq m  OBVIOUS
            <7> QED BY <7>1, <7>2
          <6>smc. s \in Messages /\ lev(s) \in Nat  BY <6>sm, <1>levfacts
          <6>4. Tran(r) \subseteq Tran(s)  BY <6>3, <6>smc, TranTrans DEF TranTrans
          <6>5. q1 \in Tran(s)  BY <5>3, <6>4
          <6>6. q1 = s  BY <4>1, <6>3, <6>5, PrevComparableEqual
          <6>7. r \in Tran(q1)  BY <6>3, <6>6
          <6>8. q1 \in Tran(r)  BY <5>3
          <6>9. q1 = r
            <7>1. q1 \in Messages  BY <4>4, <1>levfacts
            <7>2. r \in Messages  BY <5>6, <1>levfacts
            <7> QED BY <6>7, <6>8, <7>1, <7>2, TranAntisym
          <6>10. q1 \in Prev(x1) \cap Prev(x2)
            <7>1. q1 \in Prev(x2)  BY <5>3, <6>9
            <7> QED BY <4>1, <7>1
          <6>11. IncPair(x1, x2) /\ ((Prev(x1)={}/\Prev(x2)={}) \/ (Prev(x1)\cap Prev(x2)#{}))
            BY <2>x, <6>10
          <6> QED BY <6>11, <2>ne
        <5> QED BY <5>9, <5>10
      <4> QED BY <4>7, <4>8
    <3>b. CASE Prev(x1) = {}
      <4>0. Prev(x2) # {}  BY <2>nb, <3>b
      <4>1. PICK q2 \in Prev(x2) : TRUE  BY <4>0
      <4>2. q2 \in TranExclusive(x2) /\ Sig(q2) = a  BY <4>1, <2>x DEF Prev
      <4>3. q2 \in Tran(x2) /\ q2 # x2  BY <4>2 DEF TranExclusive
      <4>4. q2 \in m
        <5>1. TranExclusive(x2) \subseteq m  BY <2>x
        <5> QED BY <4>2, <5>1
      <4>mc. q2 \in Messages /\ lev(q2) \in Nat  BY <4>4, <1>levfacts
      <4>5. lev(q2) < lev(x2)  BY <2>mc, <4>2, TranExclusiveDecreasesTranSize
      <4>6. x1 \notin Tran(q2)
        <5> SUFFICES ASSUME x1 \in Tran(q2) PROVE FALSE  OBVIOUS
        <5>1. Tran(q2) \subseteq Tran(x2)  BY <4>3, <2>mc, TranTrans DEF TranTrans
        <5> QED BY <5>1, <2>x
      <4>7. CASE q2 \notin Tran(x1)
        <5>1. IncPair(x1, q2)  BY <4>2, <4>4, <4>6, <4>7, <2>x
        <5>2. lev(x1) + lev(q2) \in 0..(n-1)  BY <4>5, <4>mc, <2>lev
        <5>3. Q(lev(x1) + lev(q2))  BY <5>2
        <5> QED BY <5>1, <5>3
      <4>8. CASE q2 \in Tran(x1)
        <5>1. q2 # x1  BY <4>3, <2>x
        <5>2. q2 \in TranExclusive(x1)  BY <4>8, <5>1 DEF TranExclusive
        <5>3. PICK r \in Prev(x1) : q2 \in Tran(r)  BY <5>2, <4>2, <2>mc, PrevDom
        <5>4. r \in TranExclusive(x1) /\ Sig(r) = a  BY <5>3, <2>x DEF Prev
        <5>5. r \in Tran(x1) /\ r # x1  BY <5>4 DEF TranExclusive
        <5>6. r \in m
          <6>1. TranExclusive(x1) \subseteq m  BY <2>x
          <6> QED BY <5>4, <6>1
        <5>mc. r \in Messages /\ lev(r) \in Nat  BY <5>6, <1>levfacts
        <5>7. lev(r) < lev(x1)  BY <2>mc, <5>4, TranExclusiveDecreasesTranSize
        <5>8. x2 \notin Tran(r)
          <6> SUFFICES ASSUME x2 \in Tran(r) PROVE FALSE  OBVIOUS
          <6>1. Tran(r) \subseteq Tran(x1)  BY <5>5, <2>mc, TranTrans DEF TranTrans
          <6> QED BY <6>1, <2>x
        <5>9. CASE r \notin Tran(x2)
          <6>1. IncPair(r, x2)  BY <5>4, <5>6, <5>8, <5>9, <2>x
          <6>2. lev(r) + lev(x2) \in 0..(n-1)  BY <5>7, <5>mc, <2>lev
          <6>3. Q(lev(r) + lev(x2))  BY <6>2
          <6> QED BY <6>1, <6>3
        <5>10. CASE r \in Tran(x2)
          <6>1. r \in TranExclusive(x2)  BY <5>5, <5>10, <2>x DEF TranExclusive
          <6>2. Sig(r) = Sig(x2)  BY <5>4, <2>x
          <6>3. PICK s \in Prev(x2) : r \in Tran(s)  BY <6>1, <6>2, <2>mc, PrevDom
          <6>sm. s \in m
            <7>1. s \in TranExclusive(x2)  BY <6>3 DEF Prev
            <7>2. TranExclusive(x2) \subseteq m  OBVIOUS
            <7> QED BY <7>1, <7>2
          <6>smc. s \in Messages /\ lev(s) \in Nat  BY <6>sm, <1>levfacts
          <6>4. Tran(r) \subseteq Tran(s)  BY <6>3, <6>smc, TranTrans DEF TranTrans
          <6>5. q2 \in Tran(s)  BY <5>3, <6>4
          <6>6. q2 = s  BY <4>1, <6>3, <6>5, PrevComparableEqual
          <6>7. r \in Tran(q2)  BY <6>3, <6>6
          <6>8. q2 \in Tran(r)  BY <5>3
          <6>9. q2 = r
            <7>1. q2 \in Messages  BY <4>4, <1>levfacts
            <7>2. r \in Messages  BY <5>6, <1>levfacts
            <7> QED BY <6>7, <6>8, <7>1, <7>2, TranAntisym
          <6>10. q2 \in Prev(x1) \cap Prev(x2)
            <7>1. q2 \in Prev(x1)  BY <5>3, <6>9
            <7> QED BY <4>1, <7>1
          <6>11. IncPair(x1, x2) /\ ((Prev(x1)={}/\Prev(x2)={}) \/ (Prev(x1)\cap Prev(x2)#{}))
            BY <2>x, <6>10
          <6> QED BY <6>11, <2>ne
        <5> QED BY <5>9, <5>10
      <4> QED BY <4>7, <4>8
    <3> QED BY <3>a, <3>b
  <2> QED BY <2>base, <2>nb
<1> QED BY <1>ind, GeneralNatInduction, IsaM("blast")
====================================================================
