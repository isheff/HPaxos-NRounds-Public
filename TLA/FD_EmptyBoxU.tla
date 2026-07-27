---------------------------- MODULE FD_EmptyBoxU ----------------------------
EXTENDS HPaxosPlusCal
LOCAL INSTANCE TLAPS

LEMMA FD_EmptyBoxU == ASSUME NEW U, U = {} PROVE <>(FD_Tgt(U))
<1>1. FD_Tgt(U)  BY DEF FD_Tgt
<1> QED  BY <1>1, PTL
====================================================================
