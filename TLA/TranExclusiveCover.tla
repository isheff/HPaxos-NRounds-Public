------------------------- MODULE TranExclusiveCover -------------------------
\*   TranExclusiveRefs -> cited lemma
\*   TLAPS -> proof-only
EXTENDS MessageInterface, TranExclusiveRefs
LOCAL INSTANCE TLAPS

\* Any set between Refs(m) and TranExclusive(m) covers the exclusive
\* history: the refs part already reaches everything, and the extra
\* members' histories stay inside (transitivity + acyclicity).
LEMMA TranExclusiveCover ==
  ASSUME TypeOKMessageInterface, TranFinite, TranTrans, TranAcyclic,
         NEW m \in Messages, NEW S,
         Refs(m) \subseteq S, S \subseteq TranExclusive(m)
  PROVE TranExclusive(m) = UNION {Tran(p) : p \in S}
<1>1. TranExclusive(m) = UNION {Tran(r) : r \in Refs(m)}
  BY TranExclusiveRefs
<1>sub. TranExclusive(m) \subseteq UNION {Tran(p) : p \in S}
  <2> SUFFICES ASSUME NEW z \in TranExclusive(m)
      PROVE z \in UNION {Tran(p) : p \in S}  OBVIOUS
  <2>1. PICK r \in Refs(m) : z \in Tran(r)  BY <1>1
  <2>2. r \in S  OBVIOUS
  <2> QED BY <2>1, <2>2
<1>sup. UNION {Tran(p) : p \in S} \subseteq TranExclusive(m)
  <2> SUFFICES ASSUME NEW p \in S, NEW z \in Tran(p)
      PROVE z \in TranExclusive(m)  OBVIOUS
  <2>1. p \in TranExclusive(m)  OBVIOUS
  <2>2. p \in Tran(m)  BY <2>1 DEF TranExclusive
  <2>3. z \in Tran(m)  BY <2>2 DEF TranTrans
  <2>4. z # m
    <3>1. CASE z = m
      <4>1. m \in Tran(p)  BY <3>1
      <4>2. m \notin Tran(p)  BY <2>1 DEF TranAcyclic
      <4> QED BY <4>1, <4>2
    <3> QED BY <3>1
  <2> QED BY <2>3, <2>4 DEF TranExclusive
<1> QED BY <1>sub, <1>sup
====================================================================
