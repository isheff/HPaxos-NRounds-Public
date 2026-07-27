----------------------------- MODULE CTranLevelLE -----------------------------
EXTENDS MessageConcrete, CMinLevelDom, CTranRec, CPriorsInMC,
        CPriorsDecreasesLevel, NaturalsInduction
LOCAL INSTANCE TLAPS

LEMMA CTranLevelLE == \A x \in CMC : CTranBelowProp(x)
<1> DEFINE lev(z) == CMinLevel(z)
<1> DEFINE Q(n) == \A x \in CMC : lev(x) = n => CTranBelowProp(x)
<1> SUFFICES \A n \in Nat : Q(n)  BY CMinLevelDom DEF Q
<1> HIDE DEF Q
<1>ind. \A n \in Nat : (\A mm \in 0..(n-1) : Q(mm)) => Q(n)
  <2> USE DEF Q, CTranBelowProp
  <2> SUFFICES ASSUME NEW n \in Nat, \A mm \in 0..(n-1) : Q(mm),
                      NEW x \in CMC, lev(x) = n, NEW y \in CTran(x)
               PROVE  y \in CMC /\ lev(y) <= lev(x)
    OBVIOUS
  <2>1. CTran(x) = {x} \cup UNION {CTran(p) : p \in CPriors(x)}  BY CTranRec
  <2>2. CASE y = x  BY <2>2
  <2>3. CASE y # x
    <3>1. y \in UNION {CTran(p) : p \in CPriors(x)}  BY <2>1, <2>3
    <3>2. PICK p \in CPriors(x) : y \in CTran(p)  BY <3>1
    <3>3. p \in CMC  BY <3>2, CPriorsInMC
    <3>4. lev(p) < lev(x)  BY <3>2, CPriorsDecreasesLevel
    <3>5. lev(p) \in Nat  BY <3>3, CMinLevelDom
    <3>6. lev(p) \in 0..(n-1)  BY <3>4, <3>5
    <3>7. \A yy \in CTran(p) : yy \in CMC /\ lev(yy) <= lev(p)  BY <3>3, <3>6
    <3>8. y \in CMC /\ lev(y) <= lev(p)  BY <3>2, <3>7
    <3>9. lev(y) \in Nat  BY <3>8, CMinLevelDom
    <3> QED BY <3>8, <3>4, <3>5, <3>9
  <2> QED BY <2>2, <2>3
<1> QED BY <1>ind, GeneralNatInduction, IsaM("blast")
=============================================================================
