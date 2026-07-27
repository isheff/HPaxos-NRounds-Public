------------------------------ MODULE CGenTranRefs ------------------------------
EXTENDS MessageConcrete, CSelfInTran, CMaxLevelElement, CTranTrans,
        CTranExclDecreasesLevel, CMinLevelDom, FiniteSetTheorems

LEMMA CGenTranRefs ==
  ASSUME NEW U, IsFiniteSet(U), U \subseteq CMC, \A x \in U : CTran(x) \subseteq U
  PROVE U = UNION {CTran(x) : x \in CMMax(U)}
<1>closed. \A x \in U : CTran(x) \subseteq U  OBVIOUS
<1>sup. UNION {CTran(x) : x \in CMMax(U)} \subseteq U
  <2> SUFFICES ASSUME NEW x \in CMMax(U), NEW z \in CTran(x) PROVE z \in U  OBVIOUS
  <2>1. x \in U  BY DEF CMMax
  <2>2. CTran(x) \subseteq U  BY <2>1, <1>closed
  <2> QED BY <2>2
<1>sub. U \subseteq UNION {CTran(x) : x \in CMMax(U)}
  <2> SUFFICES ASSUME NEW z \in U PROVE z \in UNION {CTran(x) : x \in CMMax(U)}  OBVIOUS
  <2>zmc. z \in CMC  OBVIOUS
  <2>zz. z \in CTran(z)  BY <2>zmc, CSelfInTran
  <2> DEFINE cand == {y \in U : z \in CTran(y)}
  <2>c1. cand \subseteq CMC  OBVIOUS
  <2>c2. cand # {}  BY <2>zz
  <2>c3. IsFiniteSet(cand)  BY FS_Subset
  <2>x. PICK x \in cand : \A y \in cand : CMinLevel(y) <= CMinLevel(x)  BY <2>c1, <2>c2, <2>c3, CMaxLevelElement
  <2>x1. x \in U /\ z \in CTran(x)  BY <2>x
  <2>x3. x \in CMC  BY <2>x1
  <2>x4. x \in CMMax(U)
    <3> SUFFICES ASSUME NEW y \in U, x \in CTranExcl(y) PROVE FALSE
      BY <2>x1 DEF CMMax
    <3>1. y \in CMC  OBVIOUS
    <3>2. x \in CTran(y)  BY DEF CTranExcl
    <3>3. CTran(x) \subseteq CTran(y)  BY <3>1, <3>2, CTranTrans
    <3>4. z \in CTran(y)  BY <2>x1, <3>3
    <3>5. y \in cand  BY <3>4
    <3>6. CMinLevel(x) < CMinLevel(y)  BY <3>1, CTranExclDecreasesLevel
    <3>7. CMinLevel(y) <= CMinLevel(x)  BY <3>5, <2>x
    <3>8. CMinLevel(x) \in Nat /\ CMinLevel(y) \in Nat  BY <2>x3, <3>1, CMinLevelDom
    <3> QED BY <3>6, <3>7, <3>8
  <2> QED BY <2>x1, <2>x4
<1> QED BY <1>sup, <1>sub
=============================================================================
