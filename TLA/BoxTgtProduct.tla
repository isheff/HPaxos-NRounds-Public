---------------------------- MODULE BoxTgtProduct ----------------------------
EXTENDS HPaxosPlusCal, ProdEq
LOCAL INSTANCE TLAPS

LEMMA BoxTgtProduct ==
  ASSUME NEW a, NEW T
  PROVE  BTPop(a, T)
<1> USE DEF BTPop
<1>1. Init => (CP_Tgt({a} \X T) <=> (T \subseteq known_messages[a]))
  BY ProdEq DEF CP_Tgt
<1>2. (CP_Tgt({a} \X T) <=> (T \subseteq known_messages[a])) /\ [Next]_vars
        => (CP_Tgt({a} \X T) <=> (T \subseteq known_messages[a]))'
  BY ProdEq DEF CP_Tgt
<1> QED  BY <1>1, <1>2, PTL DEF Spec
====================================================================
