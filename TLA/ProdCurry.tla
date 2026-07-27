----------------------------- MODULE ProdCurry -----------------------------
EXTENDS HPaxosPlusCal

LEMMA ProdCurry ==
  ASSUME NEW AA, NEW BB, NEW kn
  PROVE  (\A p \in AA \X BB : p[2] \in kn[p[1]]) <=> (\A aa \in AA : BB \subseteq kn[aa])
<1>1. ASSUME \A p \in AA \X BB : p[2] \in kn[p[1]], NEW aa \in AA, NEW x \in BB
      PROVE x \in kn[aa]
  <2>1. <<aa, x>> \in AA \X BB  BY <1>1
  <2>2. <<aa, x>>[2] \in kn[<<aa, x>>[1]]  BY <1>1, <2>1
  <2> QED  BY <2>2
<1>2. ASSUME \A aa \in AA : BB \subseteq kn[aa], NEW p \in AA \X BB PROVE p[2] \in kn[p[1]]
  <2>1. p[1] \in AA /\ p[2] \in BB  BY <1>2
  <2> QED  BY <2>1, <1>2
<1> QED  BY <1>1, <1>2
====================================================================
