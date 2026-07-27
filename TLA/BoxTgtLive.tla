----------------------------- MODULE BoxTgtLive -----------------------------
EXTENDS HPaxosPlusCal, ProdCurry
LOCAL INSTANCE TLAPS

LEMMA BoxTgtLive == ASSUME NEW m PROVE BTLop(m)
<1> USE DEF BTLop
<1>1. Init => (CP_Tgt(LiveAcceptors \X m) <=> ELtgt(m))
  BY ProdCurry DEF CP_Tgt, ELtgt
<1>2. (CP_Tgt(LiveAcceptors \X m) <=> ELtgt(m)) /\ [Next]_vars
      => (CP_Tgt(LiveAcceptors \X m) <=> ELtgt(m))'
  BY ProdCurry DEF CP_Tgt, ELtgt
<1> QED  BY <1>1, <1>2, PTL DEF Spec
====================================================================
