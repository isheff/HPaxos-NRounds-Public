----------------------------- MODULE CLevelIndep -----------------------------
EXTENDS MessageConcrete, CGStep, CLevelIndepGen

LEMMA CLevelIndep ==
  ASSUME NEW F(_,_), NEW R(_),
         \A w \in CMC : R(w) \subseteq CMC,
         \A w \in CMC : \A y \in R(w) :
             CMinLevel(y) < CMinLevel(w),
         NEW l \in Nat, NEW x \in CMCAL[l]
  PROVE  CGFun(F, R)[l][x] = CGFun(F, R)[CMinLevel(x)][x]
<1>1. CGRec(CGFun(F, R), F, R)  BY CGStep DEF CGRec
<1> QED BY <1>1, CLevelIndepGen
=============================================================================
