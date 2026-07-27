----------------------------- MODULE CPriorsFinite -----------------------------
EXTENDS MessageConcrete, CMinLevelDom, CMCALUnfold, FiniteSetTheorems

LEMMA CPriorsFinite == \A w \in CMC : IsFiniteSet(CPriors(w))
<1> SUFFICES ASSUME NEW w \in CMC PROVE IsFiniteSet(CPriors(w))  OBVIOUS
<1> DEFINE lw == CMinLevel(w)
<1>1. lw \in Nat /\ w \in CMCAL[lw]
      /\ \A kk \in Nat : w \in CMCAL[kk] => lw <= kk  BY CMinLevelDom
<1>2. CASE lw = 0
  <2>1. w \in CMCLBase  BY <1>1, <1>2, CMCALUnfold
  <2>2. w.priors = {}  BY <2>1 DEF CMCLBase
  <2> QED BY <2>2, FS_EmptySet DEF CPriors
<1>3. CASE lw # 0
  <2>1. lw - 1 \in Nat  BY <1>1, <1>3
  <2>2. w \in CMCLExt(CMCAL[lw-1])  BY <1>1, <1>3, CMCALUnfold
  <2>3. w \notin CMCAL[lw-1]
    <3> SUFFICES ASSUME w \in CMCAL[lw-1] PROVE FALSE  OBVIOUS
    <3>1. lw <= lw - 1  BY <1>1, <2>1
    <3> QED BY <3>1, <1>1, <1>3
  <2>4. w \in CMCLNew(CMCAL[lw-1])  BY <2>2, <2>3 DEF CMCLExt
  <2>5. w.priors \in {x2 \in SUBSET CMCAL[lw-1] : IsFiniteSet(x2)}  BY <2>4 DEF CMCLNew
  <2> QED BY <2>5 DEF CPriors
<1> QED BY <1>2, <1>3
=============================================================================
