-------------------------- MODULE LearnerGraphInterface --------------------------
EXTENDS Naturals, TLAPS, SetBuilderLemmas
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE FiniteSetsExt
LOCAL INSTANCE FiniteSetTheorems
LOCAL INSTANCE Sequences

CONSTANT LearnerGraphInterface

Learners == LearnerGraphInterface.learners
Acceptors == LearnerGraphInterface.acceptors
SpecifiedSafetySets == LearnerGraphInterface.safety_sets
SpecifiedQuorums == LearnerGraphInterface.quorums

\* Instead of assuming SafetySets and Quorums are upward-closed, we'll define them that way. 
GetSpecifiedSafetySets(p) == IF p \in DOMAIN SpecifiedSafetySets
                               THEN SpecifiedSafetySets[p]
                               ELSE {}
LearnerPairs == {{pr[1], pr[2]} : pr \in Learners \X Learners}
SafetySets(p) == 
  {s \in SUBSET Acceptors :
      /\ IsFiniteSet(s)
      /\ \E m \in  GetSpecifiedSafetySets(p) : m \subseteq s}

GetSpecifiedQuorums(l) == IF l \in DOMAIN SpecifiedQuorums
                          THEN SpecifiedQuorums[l]
                          ELSE {}
Quorums(l) == 
  {s \in SUBSET Acceptors :
      /\ IsFiniteSet(s)
      /\ \E m \in GetSpecifiedQuorums(l) : m \subseteq s}

\* beta is (still) connected to alpha given the caught set: some safety set
\* of the pair has NO caught member (paper Definition 12).
ConFromCaught(alpha, caught) == {beta \in Learners :
  \E s \in SafetySets({alpha, beta}): ((s \cap caught) = {})}



\* The sequences l of subsets of Acceptors such that each element is a subset
\* of the previous element and has different ConFromCaught from the previous
\* element.
ValidSeqs(alpha) == {l \in Seq(SUBSET Acceptors) :
    \A i \in (1..(Len(l)-1)) :
      /\ l[i+1] \subseteq l[i]
      /\ ConFromCaught(alpha, l[i]) # ConFromCaught(alpha, l[i+1])}

\* The (one less than the length of) maximal length list such that:
\* each element is a subset of previous elements and a subset of acceptors
\* each element has different confromcaught from previous elements
MaxDepth(alpha) == Max({Len(s)-1 : s \in ValidSeqs(alpha)})



SafetySetsTypeOK == SpecifiedSafetySets \in [LearnerPairs -> SUBSET (SUBSET Acceptors)]
QuorumsTypeOK == SpecifiedQuorums \in [Learners -> SUBSET (SUBSET Acceptors)]
FiniteAcceptors == IsFiniteSet(Acceptors)
FiniteLearners == IsFiniteSet(Learners)
LearnersNonEmpty == Learners # {}
QuorumsNonEmpty == \A alpha \in Learners: Quorums(alpha) # {}
LearnersMightAgree == \A p \in LearnerPairs: Acceptors \in SafetySets(p)
CondensedLearnerGraphAssumption ==
  \A x \in Learners:
  \A y \in Learners:
  \A z \in Learners:
  \A xy \in SafetySets({x,y}):
  \A yz \in SafetySets({y,z}):
  (xy \cup yz) \in SafetySets({x,z})
ValidLearnerGraphAssumption ==
  \A x \in Learners :
  \A y \in Learners :
  \A s \in SafetySets({x,y}) :
  \A qx \in Quorums(x) :
  \A qy \in Quorums(y) :
  (s \cap qx \cap qy) # {}

LearnerGraphAssumptions ==
  /\ SafetySetsTypeOK
  /\ QuorumsTypeOK
  /\ FiniteAcceptors
  /\ FiniteLearners
  /\ LearnersNonEmpty
  /\ QuorumsNonEmpty 
  /\ LearnersMightAgree 
  /\ CondensedLearnerGraphAssumption
  /\ ValidLearnerGraphAssumption


LEMMA AgreementImpliesSelfAgreement ==
  (CondensedLearnerGraphAssumption
   ) => \A alpha \in Learners: \A beta \in Learners:
   SafetySets({alpha, beta}) \subseteq SafetySets({alpha, alpha})
<1> SUFFICES ASSUME CondensedLearnerGraphAssumption,
                    NEW alpha \in Learners, NEW beta \in Learners
             PROVE SafetySets({alpha, beta}) \subseteq SafetySets({alpha, alpha})
  OBVIOUS
<1> SUFFICES ASSUME NEW s \in SafetySets({alpha, beta}) PROVE s \in SafetySets({alpha, alpha})  OBVIOUS
<1>1. s \in SafetySets({beta, alpha})  OBVIOUS
<1>2. s \cup s \in SafetySets({alpha, alpha})  BY <1>1 DEF CondensedLearnerGraphAssumption
<1>3. s \cup s = s  OBVIOUS
<1> QED BY <1>2, <1>3

LEMMA AcceptorsNonEmpty ==
  (/\ LearnersNonEmpty
   /\ QuorumsNonEmpty
   /\ LearnersMightAgree
   /\ ValidLearnerGraphAssumption
   ) => Acceptors # {}
<1> SUFFICES ASSUME LearnersNonEmpty, QuorumsNonEmpty,
                    LearnersMightAgree, ValidLearnerGraphAssumption
             PROVE Acceptors # {}
  OBVIOUS
<1>ne. Learners # {}  BY DEF LearnersNonEmpty
<1>1. PICK alpha \in Learners : TRUE  BY <1>ne
<1>2. Quorums(alpha) # {}  BY <1>1 DEF QuorumsNonEmpty
<1>3. PICK q \in Quorums(alpha) : TRUE  BY <1>2
<1>4. q \subseteq Acceptors  BY <1>3 DEF Quorums
<1>5. <<alpha, alpha>> \in Learners \X Learners  BY <1>1
<1>6. {alpha, alpha} \in LearnerPairs  BY <1>5 DEF LearnerPairs
<1>7. Acceptors \in SafetySets({alpha, alpha})  BY <1>6 DEF LearnersMightAgree
<1>8. Acceptors \cap q \cap q # {}  BY <1>1, <1>3, <1>7 DEF ValidLearnerGraphAssumption
<1>9. q # {}  BY <1>8
<1> QED BY <1>4, <1>9

\* ConFromCaught is antitone: a bigger caught set only disconnects more
\* learners (an uncaught safety set for the bigger caught set is a fortiori
\* uncaught for the smaller one).
LEMMA ConFromCaughtAntitone ==
  ASSUME NEW alpha \in Learners, NEW A, NEW B, A \subseteq B
  PROVE ConFromCaught(alpha, B) \subseteq ConFromCaught(alpha, A)
<1> SUFFICES ASSUME NEW beta \in ConFromCaught(alpha, B)
             PROVE beta \in ConFromCaught(alpha, A)
  OBVIOUS
<1>1. PICK s \in SafetySets({alpha, beta}) : s \cap B = {}  BY DEF ConFromCaught
<1>2. s \cap A \subseteq s \cap B  OBVIOUS
<1>3. s \cap A = {}  BY <1>1, <1>2
<1> QED BY <1>1, <1>3 DEF ConFromCaught

\* A chain of length N of strictly-decreasing subsets of a finite set X has
\* N <= Cardinality(X) + 1 (a maximal chain runs from a set of size
\* Cardinality(X) down to the empty set).
LEMMA StrictSubsetChainBound ==
  ASSUME NEW X, IsFiniteSet(X), NEW N \in Nat, NEW l \in [1..N -> SUBSET X],
         \A i \in 1..(N-1) : l[i+1] \subseteq l[i] /\ l[i+1] # l[i]
  PROVE N <= Cardinality(X) + 1
<1>Xnat. Cardinality(X) \in Nat  BY FS_CardinalityType
<1> DEFINE Q(i) == i \in 1..N => Cardinality(l[i]) + i <= Cardinality(X) + 1
<1>allQ. \A i \in Nat : Q(i)
  <2> HIDE DEF Q
  <2>ind. \A i \in Nat : (\A k \in 0..(i-1) : Q(k)) => Q(i)
    <3> USE DEF Q
    <3> SUFFICES ASSUME NEW i \in Nat, \A k \in 0..(i-1) : Q(k), i \in 1..N
                 PROVE Cardinality(l[i]) + i <= Cardinality(X) + 1
      OBVIOUS
    <3>1. CASE i = 1
      <4>1. l[i] \in SUBSET X  OBVIOUS
      <4>2. Cardinality(l[i]) <= Cardinality(X)  BY <4>1, FS_Subset
      <4>3. Cardinality(l[i]) \in Nat  BY <4>1, FS_Subset, FS_CardinalityType
      <4> QED BY <3>1, <4>2, <4>3, <1>Xnat
    <3>2. CASE i > 1
      <4>im1. i - 1 \in 1..N  BY <3>2
      <4>ihk. i - 1 \in 0..(i-1)  OBVIOUS
      <4>ih. Q(i-1)  BY <4>ihk
      <4>ihE. Cardinality(l[i-1]) + (i-1) <= Cardinality(X) + 1  BY <4>ih, <4>im1
      <4>j. i - 1 \in 1..(N-1)  BY <3>2
      <4>sub. l[i] \subseteq l[i-1] /\ l[i] # l[i-1]  BY <4>j
      <4>l1fin. l[i-1] \in SUBSET X  BY <4>im1
      <4>l1finset. IsFiniteSet(l[i-1])  BY <4>l1fin, FS_Subset
      <4>card. Cardinality(l[i]) < Cardinality(l[i-1])  BY <4>sub, <4>l1finset, FS_Subset
      <4>types. Cardinality(l[i]) \in Nat /\ Cardinality(l[i-1]) \in Nat
        BY <4>l1finset, FS_CardinalityType, <4>sub, FS_Subset
      <4>itypes. i \in Nat /\ i >= 2  BY <3>2
      <4>im1val. i - 1 + 1 = i  BY <4>itypes
      <4> QED BY <4>ihE, <4>card, <4>types, <4>itypes, <1>Xnat, <4>im1val
    <3> QED BY <3>1, <3>2
  <2> QED BY <2>ind, GeneralNatInduction, IsaM("blast")
<1>caseZero. CASE N = 0
  <2> QED BY <1>caseZero, <1>Xnat
<1>casePos. CASE N > 0
  <2>N. N \in 1..N  BY <1>casePos
  <2>QN. Cardinality(l[N]) + N <= Cardinality(X) + 1  BY <1>allQ, <2>N
  <2>lNfin. l[N] \in SUBSET X  BY <2>N
  <2>lNfinset. IsFiniteSet(l[N])  BY <2>lNfin, FS_Subset
  <2>card0. Cardinality(l[N]) \in Nat  BY <2>lNfinset, FS_CardinalityType
  <2>Nnat. N \in Nat  OBVIOUS
  <2> QED BY <2>QN, <2>card0, <2>Nnat, <1>Xnat, <1>casePos
<1> QED BY <1>caseZero, <1>casePos

\* Any valid chain has length bounded by Cardinality(Acceptors) + 1, since
\* the l[i] themselves form a strictly-decreasing chain of subsets of
\* Acceptors.
LEMMA ValidSeqLenBoundAcceptors ==
  ASSUME FiniteAcceptors, NEW alpha \in Learners, NEW l \in ValidSeqs(alpha)
  PROVE Len(l) <= Cardinality(Acceptors) + 1
<1>1. IsFiniteSet(Acceptors)  BY DEF FiniteAcceptors
<1>2. l \in Seq(SUBSET Acceptors)  BY DEF ValidSeqs
<1>3. l \in [1..Len(l) -> SUBSET Acceptors]  BY <1>2
<1>4. Len(l) \in Nat  BY <1>2
<1>5. \A i \in 1..(Len(l)-1) : l[i+1] \subseteq l[i] /\ l[i+1] # l[i]  BY DEF ValidSeqs
<1> QED BY <1>1, <1>3, <1>4, <1>5, StrictSubsetChainBound

\* Any valid chain also has length bounded by Cardinality(Learners) + 1,
\* since ConFromCaught(alpha, l[i]) forms a strictly-INCREASING chain of
\* subsets of Learners (by ConFromCaughtAntitone: caught sets shrink along
\* the chain, so connectivity grows).  We reverse the derived sequence so
\* StrictSubsetChainBound (which wants a decreasing chain) applies.
LEMMA ValidSeqLenBoundLearners ==
  ASSUME FiniteLearners, NEW alpha \in Learners, NEW l \in ValidSeqs(alpha)
  PROVE Len(l) <= Cardinality(Learners) + 1
<1>1. IsFiniteSet(Learners)  BY DEF FiniteLearners
<1>2. l \in Seq(SUBSET Acceptors)  BY DEF ValidSeqs
<1>4. Len(l) \in Nat  BY <1>2
<1>5. \A i \in 1..(Len(l)-1) : l[i+1] \subseteq l[i] /\ ConFromCaught(alpha, l[i]) # ConFromCaught(alpha, l[i+1])
  BY DEF ValidSeqs
<1> DEFINE N == Len(l)
<1> DEFINE lp == [i \in 1..N |-> ConFromCaught(alpha, l[N + 1 - i])]
<1>ldom. l \in [1..N -> SUBSET Acceptors]  BY <1>2
<1>dom. lp \in [1..N -> SUBSET Learners]  BY DEF ConFromCaught
<1>chain. \A i \in 1..(N-1) : lp[i+1] \subseteq lp[i] /\ lp[i+1] # lp[i]
  <2> SUFFICES ASSUME NEW i \in 1..(N-1)
               PROVE lp[i+1] \subseteq lp[i] /\ lp[i+1] # lp[i]
    OBVIOUS
  <2>j. N - i \in 1..(N-1)  BY <1>4
  <2>1. l[(N-i)+1] \subseteq l[N-i]  BY <1>5, <2>j
  <2>2. ConFromCaught(alpha, l[N-i]) \subseteq ConFromCaught(alpha, l[(N-i)+1])
    BY <2>1, ConFromCaughtAntitone
  <2>3. ConFromCaught(alpha, l[N-i]) # ConFromCaught(alpha, l[(N-i)+1])  BY <1>5, <2>j
  <2>dom. i \in 1..N /\ i+1 \in 1..N  BY <1>4
  <2>i1. N + 1 - (i+1) = N - i  BY <1>4
  <2>4. lp[i+1] = ConFromCaught(alpha, l[N-i])  BY <2>dom, <2>i1
  <2>5. lp[i] = ConFromCaught(alpha, l[(N-i)+1])
    <3>1. N + 1 - i = (N - i) + 1  BY <1>4
    <3> QED BY <2>dom, <3>1
  <2> QED BY <2>2, <2>3, <2>4, <2>5
<1> QED BY <1>1, <1>dom, <1>4, <1>chain, StrictSubsetChainBound

\* Generic existence of a maximum for a finite, non-empty set of naturals.
LEMMA FiniteSetHasMax ==
  ASSUME NEW D, IsFiniteSet(D), D # {}, \A x \in D : x \in Nat
  PROVE \E r \in D : \A y \in D : y <= r
<1> DEFINE Q(n) == \A U : (IsFiniteSet(U) /\ Cardinality(U) = n /\ U # {}
                            /\ (\A z \in U : z \in Nat))
                          => (\E r \in U : \A y \in U : y <= r)
<1> SUFFICES \A n \in Nat : Q(n)
  <2>1. Cardinality(D) \in Nat  BY FS_CardinalityType
  <2> QED BY <2>1 DEF Q
<1> HIDE DEF Q
<1>ind. \A n \in Nat : (\A k \in 0..(n-1) : Q(k)) => Q(n)
  <2> USE DEF Q
  <2> SUFFICES ASSUME NEW n \in Nat, \A k \in 0..(n-1) : Q(k),
                      NEW U, IsFiniteSet(U), Cardinality(U) = n, U # {},
                      \A z \in U : z \in Nat
               PROVE  \E r \in U : \A y \in U : y <= r
    OBVIOUS
  <2>x. PICK x \in U : TRUE  OBVIOUS
  <2>pos. Cardinality(U) >= 1  BY FS_EmptySet, FS_CardinalityType
  <2>n1. n - 1 \in Nat  BY <2>pos
  <2>U2. IsFiniteSet(U \ {x}) /\ Cardinality(U \ {x}) = n - 1
    BY <2>x, FS_RemoveElement
  <2>1. CASE U \ {x} = {}
    <3>1. \A y \in U : y <= x
      <4>1. ASSUME NEW y \in U PROVE y <= x
        <5>1. y = x  BY <2>1, <4>1
        <5> QED BY <5>1
      <4> QED BY <4>1
    <3> QED BY <3>1, <2>x
  <2>2. CASE U \ {x} # {}
    <3>k. n - 1 \in 0..(n-1)  BY <2>n1
    <3>ih. \E r \in (U \ {x}) : \A y \in (U \ {x}) : y <= r
      BY <3>k, <2>U2, <2>2
    <3> PICK r \in (U \ {x}) : \A y \in (U \ {x}) : y <= r  BY <3>ih
    <3>rnat. r \in Nat  OBVIOUS
    <3>xnat. x \in Nat  BY <2>x
    <3>1. CASE x <= r
      <4> QED BY <3>1
    <3>2. CASE x > r
      <4> QED BY <3>2, <3>rnat, <3>xnat
    <3> QED BY <3>1, <3>2
  <2> QED BY <2>1, <2>2
<1> QED BY <1>ind, GeneralNatInduction, IsaM("blast")

LEMMA MaxProps ==
  ASSUME NEW D, IsFiniteSet(D), D # {}, \A x \in D : x \in Nat
  PROVE Max(D) \in D /\ (\A y \in D : Max(D) >= y)
<1>ex. \E r \in D : \A y \in D : y <= r  BY FiniteSetHasMax
<1> PICK r \in D : \A y \in D : y <= r  BY <1>ex
<1>witness. \E x \in D : \A y \in D : x >= y  OBVIOUS
<1> QED BY <1>witness DEF Max

\* Given a length bound N+1 on all valid chains (from EITHER
\* ValidSeqLenBoundAcceptors or ValidSeqLenBoundLearners) and the fact that
\* <<Acceptors,{}>> is always a valid chain of length 2, MaxDepth(alpha) is
\* sandwiched in 1..N.  Works with the set of lengths L (fully Nat-typed,
\* no subtraction) rather than the set of depths directly, since Len(s)-1
\* for the length-0 (empty) chain is not usefully typed.
LEMMA MaxDepthBound ==
  ASSUME NEW alpha \in Learners, NEW N \in Nat,
         \A l \in ValidSeqs(alpha) : Len(l) <= N + 1,
         <<Acceptors, {}>> \in ValidSeqs(alpha)
  PROVE MaxDepth(alpha) \in 1..N
<1> DEFINE L == {Len(s) : s \in ValidSeqs(alpha)}
<1>witlen. Len(<<Acceptors, {}>>) = 2  OBVIOUS
<1>l2. 2 \in L  BY <1>witlen
<1>rangefin. IsFiniteSet(0..(N+1))  BY FS_Interval
<1>lsub. L \subseteq 0..(N+1)
  <2> SUFFICES ASSUME NEW k \in L PROVE k \in 0..(N+1)  OBVIOUS
  <2>1. PICK s \in ValidSeqs(alpha) : k = Len(s)  OBVIOUS
  <2>2. Len(s) \in Nat  BY <2>1 DEF ValidSeqs
  <2>3. Len(s) <= N + 1  BY <2>1
  <2> QED BY <2>1, <2>2, <2>3
<1>Lfin. IsFiniteSet(L)  BY <1>lsub, <1>rangefin, FS_Subset
<1>Lne. L # {}  BY <1>l2
<1>Lnat. \A x \in L : x \in Nat  BY <1>lsub
<1>maxprops. Max(L) \in L /\ (\A y \in L : Max(L) >= y)  BY <1>Lfin, <1>Lne, <1>Lnat, MaxProps
<1>MaxLinL. Max(L) \in L  BY <1>maxprops
<1>MaxLge2. Max(L) >= 2  BY <1>maxprops, <1>l2
<1>MaxLnat. Max(L) \in Nat  BY <1>MaxLinL, <1>lsub
<1>MaxLle. Max(L) <= N + 1  BY <1>MaxLinL, <1>lsub
<1> PICK sm \in ValidSeqs(alpha) : Len(sm) = Max(L)  BY <1>MaxLinL
<1>smnat. Len(sm) \in Nat  BY DEF ValidSeqs
<1>d_witness. Max(L) - 1 \in {Len(s)-1 : s \in ValidSeqs(alpha)}  OBVIOUS
<1>d_upper. \A d \in {Len(s)-1 : s \in ValidSeqs(alpha)} : d <= Max(L) - 1
  <2> SUFFICES ASSUME NEW d \in {Len(s)-1 : s \in ValidSeqs(alpha)} PROVE d <= Max(L) - 1  OBVIOUS
  <2>1. PICK s \in ValidSeqs(alpha) : d = Len(s)-1  OBVIOUS
  <2>2. Len(s) \in L  BY <2>1
  <2>3. Len(s) <= Max(L)  BY <2>2, <1>maxprops
  <2>4. Len(s) \in Nat  BY <2>1 DEF ValidSeqs
  <2> QED BY <2>1, <2>3, <2>4, <1>MaxLnat
<1>witness2. \E x \in {Len(s)-1 : s \in ValidSeqs(alpha)} : \A y \in {Len(s)-1 : s \in ValidSeqs(alpha)} : x >= y
  BY <1>d_witness, <1>d_upper
<1>maxprops2. MaxDepth(alpha) \in {Len(s)-1 : s \in ValidSeqs(alpha)}
              /\ (\A y \in {Len(s)-1 : s \in ValidSeqs(alpha)} : MaxDepth(alpha) >= y)
  BY <1>witness2 DEF MaxDepth, Max
<1>maxLm1nat. Max(L) - 1 \in Nat  BY <1>MaxLge2, <1>MaxLnat
<1>upper_bnd. Max(L) - 1 <= MaxDepth(alpha)  BY <1>maxprops2, <1>d_witness
<1>lower_bnd. MaxDepth(alpha) <= Max(L) - 1  BY <1>maxprops2, <1>d_upper
<1> PICK sw \in ValidSeqs(alpha) : MaxDepth(alpha) = Len(sw) - 1  BY <1>maxprops2
<1>swnat. Len(sw) \in Nat  BY DEF ValidSeqs
<1>swmd. MaxDepth(alpha) = Len(sw) - 1  OBVIOUS
<1>swge2. Len(sw) >= 2  BY <1>upper_bnd, <1>swnat, <1>maxLm1nat, <1>MaxLge2, <1>MaxLnat, <1>swmd
<1>mdnat. MaxDepth(alpha) \in Nat  BY <1>swge2, <1>swnat
<1> QED BY <1>upper_bnd, <1>lower_bnd, <1>mdnat, <1>MaxLge2, <1>MaxLnat, <1>MaxLle

\* <<Acceptors,{}>> is always a valid chain of depth 1: ConFromCaught at
\* Acceptors is empty (no safety set is disjoint from all of Acceptors --
\* the empty set is ruled out as a safety set by ValidLearnerGraphAssumption
\* plus QuorumsNonEmpty), which differs from ConFromCaught at {} (all of
\* Learners, by LearnersMightAgree), given Learners is non-empty.
LEMMA LowerBoundWitness ==
  ASSUME LearnersMightAgree, QuorumsNonEmpty, ValidLearnerGraphAssumption,
         NEW alpha \in Learners, Acceptors # {}, Learners # {}
  PROVE <<Acceptors, {}>> \in ValidSeqs(alpha)
<1>seq. <<Acceptors, {}>> \in Seq(SUBSET Acceptors)  OBVIOUS
<1>full. \A beta \in Learners : Acceptors \in SafetySets({alpha, beta})
  <2> SUFFICES ASSUME NEW beta \in Learners PROVE Acceptors \in SafetySets({alpha, beta})  OBVIOUS
  <2>1. <<alpha, beta>> \in Learners \X Learners  OBVIOUS
  <2>2. {alpha, beta} \in LearnerPairs  BY <2>1 DEF LearnerPairs
  <2> QED BY <2>2 DEF LearnersMightAgree
<1>noempty. \A beta \in Learners : {} \notin SafetySets({alpha, beta})
  <2> SUFFICES ASSUME NEW beta \in Learners, {} \in SafetySets({alpha, beta})
               PROVE FALSE
    OBVIOUS
  <2>1. PICK q \in Quorums(alpha) : TRUE  BY DEF QuorumsNonEmpty
  <2>2. PICK r \in Quorums(beta) : TRUE  BY DEF QuorumsNonEmpty
  <2>3. ({} \cap q \cap r) # {}  BY <2>1, <2>2 DEF ValidLearnerGraphAssumption
  <2> QED BY <2>3
<1>con. ConFromCaught(alpha, Acceptors) = {}
  <2> SUFFICES ASSUME NEW beta \in ConFromCaught(alpha, Acceptors)
               PROVE FALSE
    OBVIOUS
  <2>1. PICK s \in SafetySets({alpha, beta}) : s \cap Acceptors = {}  BY DEF ConFromCaught
  <2>2. s \subseteq Acceptors  BY <2>1 DEF SafetySets
  <2>3. s = {}  BY <2>1, <2>2
  <2>4. beta \in Learners  BY DEF ConFromCaught
  <2> QED BY <2>1, <2>3, <2>4, <1>noempty
<1>con0. ConFromCaught(alpha, {}) = Learners
  <2>1. \A beta \in Learners : beta \in ConFromCaught(alpha, {})
    <3> SUFFICES ASSUME NEW beta \in Learners PROVE beta \in ConFromCaught(alpha, {})  OBVIOUS
    <3>1. Acceptors \in SafetySets({alpha, beta})  BY <1>full
    <3>2. Acceptors \cap {} = {}  OBVIOUS
    <3> QED BY <3>1, <3>2 DEF ConFromCaught
  <2> QED BY <2>1 DEF ConFromCaught
<1>diff. ConFromCaught(alpha, Acceptors) # ConFromCaught(alpha, {})  BY <1>con, <1>con0
<1>sub. {} \subseteq Acceptors  OBVIOUS
<1>idx. 1 .. (Len(<<Acceptors, {}>>) - 1) = {1}  OBVIOUS
<1>chain. \A i \in 1..(Len(<<Acceptors, {}>>)-1) :
             <<Acceptors, {}>>[i+1] \subseteq <<Acceptors, {}>>[i]
             /\ ConFromCaught(alpha, <<Acceptors, {}>>[i]) # ConFromCaught(alpha, <<Acceptors, {}>>[i+1])
  BY <1>idx, <1>sub, <1>diff
<1> QED BY <1>seq, <1>chain DEF ValidSeqs

LEMMA MaxDepthFiniteAcceptors ==
  (/\ FiniteAcceptors
   /\ LearnersNonEmpty
   /\ QuorumsNonEmpty
   /\ LearnersMightAgree
   /\ ValidLearnerGraphAssumption
   ) => \A alpha \in Learners:
  MaxDepth(alpha) \in (1..Cardinality(Acceptors))
<1> SUFFICES ASSUME FiniteAcceptors, LearnersNonEmpty, QuorumsNonEmpty,
                    LearnersMightAgree, ValidLearnerGraphAssumption,
                    NEW alpha \in Learners
             PROVE MaxDepth(alpha) \in (1..Cardinality(Acceptors))
  OBVIOUS
<1>accne. Acceptors # {}  BY AcceptorsNonEmpty
<1>lne. Learners # {}  BY DEF LearnersNonEmpty
<1>witness. <<Acceptors, {}>> \in ValidSeqs(alpha)  BY <1>accne, <1>lne, LowerBoundWitness
<1>accfin. IsFiniteSet(Acceptors)  BY DEF FiniteAcceptors
<1>cardnat. Cardinality(Acceptors) \in Nat  BY <1>accfin, FS_CardinalityType
<1>bound. \A l \in ValidSeqs(alpha) : Len(l) <= Cardinality(Acceptors) + 1
  <2> SUFFICES ASSUME NEW l \in ValidSeqs(alpha) PROVE Len(l) <= Cardinality(Acceptors) + 1  OBVIOUS
  <2> QED BY ValidSeqLenBoundAcceptors
<1> QED BY <1>bound, <1>witness, <1>cardnat, MaxDepthBound

LEMMA MaxDepthFiniteLearners ==
  (/\ FiniteLearners
   /\ LearnersNonEmpty
   /\ QuorumsNonEmpty
   /\ LearnersMightAgree
   /\ ValidLearnerGraphAssumption
   ) => \A alpha \in Learners:
  MaxDepth(alpha) \in (1..Cardinality(Learners))
<1> SUFFICES ASSUME FiniteLearners, LearnersNonEmpty, QuorumsNonEmpty,
                    LearnersMightAgree, ValidLearnerGraphAssumption,
                    NEW alpha \in Learners
             PROVE MaxDepth(alpha) \in (1..Cardinality(Learners))
  OBVIOUS
<1>lnefin. IsFiniteSet(Learners)  BY DEF FiniteLearners
<1>lne. Learners # {}  BY DEF LearnersNonEmpty
<1>accne. Acceptors # {}  BY AcceptorsNonEmpty
<1>witness. <<Acceptors, {}>> \in ValidSeqs(alpha)  BY <1>accne, <1>lne, LowerBoundWitness
<1>cardnat. Cardinality(Learners) \in Nat  BY <1>lnefin, FS_CardinalityType
<1>bound. \A l \in ValidSeqs(alpha) : Len(l) <= Cardinality(Learners) + 1
  <2> SUFFICES ASSUME NEW l \in ValidSeqs(alpha) PROVE Len(l) <= Cardinality(Learners) + 1  OBVIOUS
  <2> QED BY ValidSeqLenBoundLearners
<1> QED BY <1>bound, <1>witness, <1>cardnat, MaxDepthBound
====================================================================


