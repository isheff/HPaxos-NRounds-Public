------------------------------ MODULE CTranTrans ------------------------------
EXTENDS MessageConcrete, CMinLevelDom, CTranRec, CPriorsInMC,
        CPriorsDecreasesLevel, NaturalsInduction
LOCAL INSTANCE TLAPS

LEMMA CTranTrans ==
  ASSUME NEW m \in CMC,
         NEW x \in CTran(m)
  PROVE CTran(x) \subseteq CTran(m)
<1> DEFINE lev(z) == CMinLevel(z)
<1> DEFINE Q(n) == \A mm \in CMC : lev(mm) = n =>
                     \A y \in CTran(mm) : CTran(y) \subseteq CTran(mm)
<1> SUFFICES \A n \in Nat : Q(n)  BY CMinLevelDom DEF Q
<1> HIDE DEF Q
<1>ind. \A n \in Nat : (\A kk \in 0..(n-1) : Q(kk)) => Q(n)
  <2> USE DEF Q
  <2> SUFFICES ASSUME NEW n \in Nat, \A kk \in 0..(n-1) : Q(kk),
                      NEW mm \in CMC, lev(mm) = n,
                      NEW y \in CTran(mm)
               PROVE  CTran(y) \subseteq CTran(mm)
    OBVIOUS
  <2>1. CTran(mm) = {mm} \cup UNION {CTran(p) : p \in CPriors(mm)}  BY CTranRec
  <2>2. CASE y = mm  BY <2>2
  <2>3. CASE y # mm
    <3>1. y \in UNION {CTran(p) : p \in CPriors(mm)}  BY <2>1, <2>3
    <3>2. PICK p \in CPriors(mm) : y \in CTran(p)  BY <3>1
    <3>3. p \in CMC  BY <3>2, CPriorsInMC
    <3>4. lev(p) < lev(mm)  BY <3>2, CPriorsDecreasesLevel
    <3>5. lev(p) \in Nat  BY <3>3, CMinLevelDom
    <3>6. lev(p) \in 0..(n-1)  BY <3>4, <3>5
    <3>7. CTran(y) \subseteq CTran(p)  BY <3>2, <3>3, <3>6
    <3>8. CTran(p) \in {CTran(pp) : pp \in CPriors(mm)}  BY <3>2
    <3>9. CTran(p) \subseteq CTran(mm)  BY <3>8, <2>1
    <3> QED BY <3>7, <3>9
  <2> QED BY <2>2, <2>3
<1> QED BY <1>ind, GeneralNatInduction, IsaM("blast")
=============================================================================
