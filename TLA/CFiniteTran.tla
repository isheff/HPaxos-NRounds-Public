------------------------------ MODULE CFiniteTran ------------------------------
EXTENDS MessageConcrete, CMinLevelDom, CTranRec, CPriorsInMC,
        CPriorsDecreasesLevel, CPriorsFinite, FiniteSetTheorems, NaturalsInduction
LOCAL INSTANCE TLAPS

LEMMA CFiniteTran ==
  ASSUME NEW m \in CMC
  PROVE IsFiniteSet(CTran(m))
<1> DEFINE lev(z) == CMinLevel(z)
<1> DEFINE Q(n) == \A x \in CMC : lev(x) = n => IsFiniteSet(CTran(x))
<1> SUFFICES \A n \in Nat : Q(n)  BY CMinLevelDom DEF Q
<1> HIDE DEF Q
<1>ind. \A n \in Nat : (\A mm \in 0..(n-1) : Q(mm)) => Q(n)
  <2> USE DEF Q
  <2> SUFFICES ASSUME NEW n \in Nat, \A mm \in 0..(n-1) : Q(mm),
                      NEW x \in CMC, lev(x) = n
               PROVE  IsFiniteSet(CTran(x))
    OBVIOUS
  <2>1. CTran(x) = {x} \cup UNION {CTran(p) : p \in CPriors(x)}  BY CTranRec
  <2>2. IsFiniteSet({x})  BY FS_Singleton
  <2>3. IsFiniteSet(CPriors(x))  BY CPriorsFinite
  <2>4. IsFiniteSet({CTran(p) : p \in CPriors(x)})  BY <2>3, FS_Image
  <2>5. \A T \in {CTran(p) : p \in CPriors(x)} : IsFiniteSet(T)
    <3>1. ASSUME NEW T \in {CTran(p) : p \in CPriors(x)} PROVE IsFiniteSet(T)
      <4>1. PICK p \in CPriors(x) : T = CTran(p)  BY <3>1
      <4>2. p \in CMC  BY CPriorsInMC
      <4>3. lev(p) < lev(x)  BY CPriorsDecreasesLevel
      <4>4. lev(p) \in Nat  BY <4>2, CMinLevelDom
      <4>5. lev(p) \in 0..(n-1)  BY <4>3, <4>4
      <4>6. IsFiniteSet(CTran(p))  BY <4>2, <4>5
      <4> QED BY <4>1, <4>6
    <3> QED BY <3>1
  <2>6. IsFiniteSet(UNION {CTran(p) : p \in CPriors(x)})  BY <2>4, <2>5, FS_UNION
  <2> QED BY <2>1, <2>2, <2>6, FS_Union
<1> QED BY <1>ind, GeneralNatInduction, IsaM("blast")
=============================================================================
