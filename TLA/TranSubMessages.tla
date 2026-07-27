------------------------ MODULE TranSubMessages ------------------------
\* Statement and proof use only MessageInterface definitions
\* (TypeOKMessageInterface, Messages, Tran). No theorems are cited, so no
\* other import is needed.
EXTENDS MessageInterface

\* Every message in the transitive closure of m is itself a message.
LEMMA TranSubMessages ==
    ASSUME TypeOKMessageInterface, NEW x \in Messages
    PROVE Tran(x) \subseteq Messages
<1>1. MessageInterface.tran \in [Messages -> SUBSET Messages]
    BY DEF TypeOKMessageInterface
<1>2. MessageInterface.tran[x] \subseteq Messages  BY <1>1
<1> QED BY <1>2 DEF Tran
====================================================================
