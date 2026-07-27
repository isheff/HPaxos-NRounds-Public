------------------------------ MODULE CMCAcyclic ------------------------------
EXTENDS MessageConcrete, CTranExclDecreasesLevel, CTranLevelLE, CMinLevelDom

LEMMA CMCAcyclic ==
  ASSUME NEW m \in CMC, NEW p \in CTranExcl(m)
  PROVE  ~(m \in CTran(p))
<1>1. CMinLevel(p) < CMinLevel(m)  BY CTranExclDecreasesLevel
<1>2. p \in CMC
  <2>1. p \in CTran(m)  BY DEF CTranExcl
  <2> QED BY <2>1, CTranLevelLE DEF CTranBelowProp
<1> SUFFICES ASSUME m \in CTran(p) PROVE FALSE  OBVIOUS
<1>3. m \in CMC /\ CMinLevel(m) <= CMinLevel(p)
  BY <1>2, CTranLevelLE DEF CTranBelowProp
<1>4. CMinLevel(p) \in Nat  BY <1>2, CMinLevelDom
<1>5. CMinLevel(m) \in Nat  BY CMinLevelDom
<1> QED BY <1>1, <1>3, <1>4, <1>5
=============================================================================
