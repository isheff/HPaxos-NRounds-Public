--------------------- MODULE CTranExclDecreasesLevel ---------------------
EXTENDS MessageConcrete, CTranRec, CPriorsInMC, CPriorsDecreasesLevel,
        CTranLevelLE, CMinLevelDom

LEMMA CTranExclDecreasesLevel ==
  ASSUME NEW x \in CMC,
         NEW y \in CTranExcl(x)
  PROVE CMinLevel(y) < CMinLevel(x)
<1>1. y \in CTran(x) /\ y # x  BY DEF CTranExcl
<1>2. CTran(x) = {x} \cup UNION {CTran(p) : p \in CPriors(x)}  BY CTranRec
<1>3. y \in UNION {CTran(p) : p \in CPriors(x)}  BY <1>1, <1>2
<1>4. PICK p \in CPriors(x) : y \in CTran(p)  BY <1>3
<1>5. p \in CMC  BY <1>4, CPriorsInMC
<1>6. CMinLevel(p) < CMinLevel(x)  BY <1>4, CPriorsDecreasesLevel
<1>7. \A yy \in CTran(p) : yy \in CMC /\ CMinLevel(yy) <= CMinLevel(p)
  BY <1>5, CTranLevelLE DEF CTranBelowProp
<1>8. y \in CMC /\ CMinLevel(y) <= CMinLevel(p)  BY <1>4, <1>7
<1>9. CMinLevel(p) \in Nat  BY <1>5, CMinLevelDom
<1>10. CMinLevel(y) \in Nat  BY <1>8, CMinLevelDom
<1>11. CMinLevel(x) \in Nat  BY CMinLevelDom
<1> QED BY <1>6, <1>8, <1>9, <1>10, <1>11
=============================================================================
