---------------------------- MODULE IsTwoADigest ----------------------------
\*   LrnsRec -> cited lemma
\*   TLAPS -> proof-only
EXTENDS RecursiveWellFormed, LrnsRec
LOCAL INSTANCE TLAPS

\* IsTwoA read off the digest: a non-proposal with a non-empty lrns field.
LEMMA IsTwoADigest ==
  ASSUME MessageInterfaceAssumptions,
         LearnersMightAgree, ValidLearnerGraphAssumption,
         NEW m \in Messages
  PROVE IsTwoA(m) <=> (~IsProposal(m) /\ DigestLrns(m) # {})
<1>1. DigestLrns(m) = Lrns(m)  BY LrnsRec
<1>2. IsTwoA(m) = (~IsProposal(m) /\ \E alpha \in Learners : HasDepth(alpha, m, 1))
  BY DEF IsTwoA
<1>3. (Lrns(m) # {}) <=> (\E alpha \in Learners : HasDepth(alpha, m, 1))
  BY DEF Lrns
<1> QED BY <1>1, <1>2, <1>3
====================================================================
