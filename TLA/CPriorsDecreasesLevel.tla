------------------------ MODULE CPriorsDecreasesLevel ------------------------
EXTENDS MessageConcrete, CMinLevelDom, CMCALUnfold

LEMMA CPriorsDecreasesLevel ==
  ASSUME NEW x \in CMC,
         NEW y \in CPriors(x)
  PROVE CMinLevel(y) < CMinLevel(x)
<1> DEFINE lx == CMinLevel(x)
<1>1. lx \in Nat /\ x \in CMCAL[lx]
      /\ \A kk \in Nat : x \in CMCAL[kk] => lx <= kk
  BY CMinLevelDom
<1>2. y \in x.priors  BY DEF CPriors
<1>3. lx # 0
  <2> SUFFICES ASSUME lx = 0 PROVE FALSE  OBVIOUS
  <2>1. x \in CMCLBase  BY <1>1, CMCALUnfold
  <2>2. x.priors = {}  BY <2>1 DEF CMCLBase
  <2> QED BY <1>2, <2>2
<1>4. lx - 1 \in Nat  BY <1>1, <1>3
<1>5. x \in CMCLExt(CMCAL[lx-1])  BY <1>1, <1>3, CMCALUnfold
<1>6. x \notin CMCAL[lx-1]
  <2> SUFFICES ASSUME x \in CMCAL[lx-1] PROVE FALSE  OBVIOUS
  <2>1. lx <= lx - 1  BY <1>1, <1>4
  <2> QED BY <2>1, <1>1, <1>3
<1>7. x \in CMCLNew(CMCAL[lx-1])  BY <1>5, <1>6 DEF CMCLExt
<1>8. x.priors \subseteq CMCAL[lx-1]
  <2>1. x.priors \in {x2 \in SUBSET CMCAL[lx-1] : IsFiniteSet(x2)}
    BY <1>7 DEF CMCLNew
  <2> QED BY <2>1
<1>9. y \in CMCAL[lx-1]  BY <1>2, <1>8
<1>10. y \in CMC  BY <1>4, <1>9 DEF CMC
<1>11. CMinLevel(y) <= lx - 1  BY <1>4, <1>9, <1>10, CMinLevelDom
<1>12. CMinLevel(y) \in Nat  BY <1>10, CMinLevelDom
<1> QED BY <1>11, <1>12, <1>1, <1>3, <1>4
=============================================================================
