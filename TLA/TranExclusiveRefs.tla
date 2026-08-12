------------------------ MODULE TranExclusiveRefs ------------------------
\*   TranRefs -> cited lemma
\*   TLAPS    -> proof-only
EXTENDS MessageInterface, TranRefs
LOCAL INSTANCE TLAPS

\* The exclusive transitive history decomposes over the refs: acyclicity
\* rules m itself out of the union, so dropping {m} from TranRefs' equation
\* leaves exactly the union of the refs' (inclusive) histories.
LEMMA TranExclusiveRefs ==
  ASSUME TypeOKMessageInterface, TranFinite, TranTrans, TranAcyclic,
         NEW m \in Messages
  PROVE TranExclusive(m) = UNION {Tran(r) : r \in Refs(m)}
<1>1. Tran(m) = {m} \cup UNION {Tran(r) : r \in Refs(m)}  BY TranRefs
<1>2. m \notin UNION {Tran(r) : r \in Refs(m)}
  <2> SUFFICES ASSUME NEW r \in Refs(m), m \in Tran(r) PROVE FALSE  OBVIOUS
  <2>1. r \in TranExclusive(m)  BY DEF Refs
  <2> QED BY <2>1 DEF TranAcyclic
<1> QED BY <1>1, <1>2 DEF TranExclusive
====================================================================
