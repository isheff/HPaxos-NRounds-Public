--------------------------- MODULE CMMaxAddTop ---------------------------
\* Adding an element whose whole history IS the set collapses the antichain to
\* that element.  This is the post-send case: the message just sent dominates
\* everything its sender knew or had sent.
EXTENDS HPaxosPlusCalConcrete, CFields, CMessagesSubMC, CTranResolve,
        CTranAcyclic, TLAPS

LEMMA CMMaxAddTop ==
  ASSUME ConcreteMessageInterface,
         NEW U, U \subseteq Messages,
         NEW c \in Messages, TranExclusive(c) = U
  PROVE  CMMax(U \cup {c}) = {c}
<1>cmi. MessageInterface = CMI
  BY DEF ConcreteMessageInterface
<1>msg. Messages = CMessages
  BY <1>cmi, CFields
<1>cmc. c \in CMC
  BY <1>msg, CMessagesSubMC
<1>ctr. CTranExcl(c) = U
  <2>1. Tran(c) = CTran(c)
    BY <1>cmi, <1>msg, CTranResolve
  <2> QED
    BY <2>1 DEF TranExclusive, CTranExcl
<1>notin. c \notin U
  BY <1>ctr DEF CTranExcl
<1>out. \A z \in U : z \notin CMMax(U \cup {c})
  BY <1>ctr DEF CMMax
\* c itself survives: acyclicity forbids anything in U being above it.
<1>in. c \in CMMax(U \cup {c})
  <2> SUFFICES ASSUME NEW y \in U \cup {c}, c \in CTranExcl(y)
               PROVE  FALSE
    BY DEF CMMax
  <2>1. y # c
    BY DEF CTranExcl
  <2>2. y \in U
    BY <2>1
  <2>3. y \in TranExclusive(c)
    BY <2>2
  <2>4. c \notin Tran(y)
    BY <1>cmi, <2>3, CTranAcyclic DEF TranAcyclic
  <2>5. Tran(y) = CTran(y)
    BY <1>cmi, <1>msg, <2>2, CTranResolve
  <2> QED
    BY <2>4, <2>5 DEF CTranExcl
<1> QED
  BY <1>out, <1>in DEF CMMax
=============================================================================
