------------------------------- MODULE ProdEq -------------------------------
EXTENDS HPaxosPlusCal

\* Product-set equivalence (explicit tuple reasoning; SMT/auto fail on it).
LEMMA ProdEq ==
  ASSUME NEW a, NEW T, NEW kn
  PROVE  (\A p \in {a} \X T : p[2] \in kn[p[1]]) <=> (T \subseteq kn[a])
<1>1. ASSUME \A p \in {a} \X T : p[2] \in kn[p[1]], NEW w \in T PROVE w \in kn[a]
  <2>1. <<a, w>> \in {a} \X T  BY <1>1
  <2>2. <<a, w>>[2] \in kn[<<a, w>>[1]]  BY <1>1, <2>1
  <2> QED  BY <2>2
<1>2. ASSUME T \subseteq kn[a], NEW p \in {a} \X T PROVE p[2] \in kn[p[1]]
  <2>1. p[1] = a /\ p[2] \in T  BY <1>2
  <2> QED  BY <2>1, <1>2
<1> QED  BY <1>1, <1>2
====================================================================
