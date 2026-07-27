---------------------------- MODULE CaughtPrev ----------------------------
EXTENDS MessageInterface, CaughtPrevHard, CaughtPrevEasy

\* Since MI has no well-formedness axiom ruling out "Prev has multiple
\* incomparable elements", the natural HPaxos.tla-style target
\* Prev(m1)=Prev(m2) is not always derivable, and a plain
\* Prev(m1) \cap Prev(m2) # {} target is not always TRUE: two "genesis"
\* same-signer messages with disjoint, empty histories are Caught but have
\* Prev(x1)=Prev(x2)={}. The (both empty) \/ (intersection) disjunction is
\* correct in both directions without needing well-formedness.
THEOREM CaughtPrev ==
  ASSUME TypeOKMessageInterface, TranFinite, TranTrans, TranAcyclic, NEW m \in SUBSET Messages,
         \A x \in m : Tran(x) \subseteq m
  PROVE CaughtS(m) = {a \in Acceptors :
    \E m1 \in m :
    \E m2 \in m :
      /\ Sig(m1) = a
      /\ Sig(m2) = a
      /\ m1 # m2
      /\ ((Prev(m1) = {} /\ Prev(m2) = {}) \/ (Prev(m1) \cap Prev(m2) # {}))}
<1> DEFINE Target == {a \in Acceptors :
    \E m1 \in m : \E m2 \in m :
      /\ Sig(m1) = a /\ Sig(m2) = a /\ m1 # m2
      /\ ((Prev(m1) = {} /\ Prev(m2) = {}) \/ (Prev(m1) \cap Prev(m2) # {}))}
<1>mM. m \subseteq Messages  OBVIOUS
<1>te. \A xx \in m : TranExclusive(xx) \subseteq m  BY DEF TranExclusive
<1>1. CaughtS(m) \subseteq Target
  <2> SUFFICES ASSUME NEW a \in CaughtS(m) PROVE a \in Target  OBVIOUS
  <2>1. a \in Acceptors  BY DEF CaughtS
  <2>2. PICK m1 \in m, m2 \in m : Sig(m1)=a /\ Sig(m2)=a /\ m1 \notin Tran(m2) /\ m2 \notin Tran(m1)
    BY DEF CaughtS
  <2>3. \E q1 \in m: \E q2 \in m: Sig(q1)=a /\ Sig(q2)=a /\ q1 # q2 /\
          ((Prev(q1)={}/\Prev(q2)={}) \/ (Prev(q1)\cap Prev(q2)#{}))
    BY <2>1, <2>2, <1>te, CaughtPrevHard
  <2> QED BY <2>1, <2>3
<1>2. Target \subseteq CaughtS(m)
  <2> SUFFICES ASSUME NEW a \in Target PROVE a \in CaughtS(m)  OBVIOUS
  <2>1. a \in Acceptors  OBVIOUS
  <2>2. PICK m1 \in m, m2 \in m : Sig(m1)=a /\ Sig(m2)=a /\ m1#m2 /\
          ((Prev(m1)={}/\Prev(m2)={}) \/ (Prev(m1)\cap Prev(m2)#{}))  OBVIOUS
  <2>3. m1 \in Messages /\ m2 \in Messages  BY <2>2, <1>mM
  <2>4. m1 \notin Tran(m2) /\ m2 \notin Tran(m1)  BY <2>1, <2>2, <2>3, CaughtPrevEasy
  <2> QED BY <2>1, <2>2, <2>4 DEF CaughtS
<1> QED BY <1>1, <1>2
====================================================================
