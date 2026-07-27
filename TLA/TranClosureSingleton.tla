----------------------- MODULE TranClosureSingleton -----------------------
EXTENDS MessageInterface

LEMMA TranClosureSingleton == ASSUME NEW q PROVE TranClosure({q}) = Tran(q)
BY DEF TranClosure
====================================================================
