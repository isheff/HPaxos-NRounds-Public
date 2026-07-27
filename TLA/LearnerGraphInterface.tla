-------------------------- MODULE LearnerGraphInterface --------------------------
\* MUST be EXTENDS, not LOCAL INSTANCE. LOCAL INSTANCE gives this module its
\* OWN private copy of IsFiniteSet/Seq/Len/Max, so a definition like
\* FiniteAcceptors == IsFiniteSet(Acceptors) unfolds, in any OTHER module, to
\* an operator that module cannot see. SANY renames the two apart
\* (IsFiniteSet vs IsFiniteSet_1) and every proof that unfolds a definition
\* from here then fails. EXTENDS shares one copy; INSTANCE copies.
EXTENDS FiniteSetsExt, Sequences

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
====================================================================