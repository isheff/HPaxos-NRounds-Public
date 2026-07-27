--------------------- MODULE CaughtSAddNonAcceptor ---------------------
EXTENDS MessageInterface

LEMMA CaughtSAddNonAcceptor ==
  ASSUME TypeOKMessageInterface, NEW M \in SUBSET Messages, NEW q, Sig(q) \notin Acceptors
  PROVE CaughtS(M \cup {q}) = CaughtS(M)
<1>fwd. CaughtS(M) \subseteq CaughtS(M \cup {q})  BY DEF CaughtS
<1>bwd. CaughtS(M \cup {q}) \subseteq CaughtS(M)
  <2> SUFFICES ASSUME NEW s \in CaughtS(M \cup {q}) PROVE s \in CaughtS(M)  OBVIOUS
  <2>1. PICK m1 \in M \cup {q}, m2 \in M \cup {q} :
          /\ Sig(m1) = s /\ Sig(m2) = s
          /\ m1 \notin Tran(m2) /\ m2 \notin Tran(m1)
    BY DEF CaughtS
  <2>sacc. s \in Acceptors  BY <2>1 DEF CaughtS
  <2>2. m1 # q  BY <2>1, <2>sacc
  <2>3. m2 # q  BY <2>1, <2>sacc
  <2>4. m1 \in M /\ m2 \in M  BY <2>1, <2>2, <2>3
  <2> QED BY <2>1, <2>4, <2>sacc DEF CaughtS
<1> QED BY <1>fwd, <1>bwd
====================================================================
