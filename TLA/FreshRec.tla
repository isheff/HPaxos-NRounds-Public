------------------------------ MODULE FreshRec ------------------------------
\*   DigestInv, FreshResolve, DigestRec -> cited lemmas
\*   TLAPS -> proof-only
EXTENDS RecursiveWellFormed, DigestInv, FreshResolve, DigestRec
LOCAL INSTANCE TLAPS

\* The assembled fresh field decides Fresh exactly. (Corollary: DigestInv
\* supplies the highesttwoas correctness FreshResolve needs, at
\* S := Refs(m).)
LEMMA FreshRec ==
  ASSUME MessageInterfaceAssumptions,
         LearnersMightAgree, ValidLearnerGraphAssumption,
         NEW m \in Messages, NEW alpha \in Learners
  PROVE DigestFresh(m)[alpha] <=> Fresh(alpha, m)
<1>tok. TypeOKMessageInterface  BY DEF MessageInterfaceAssumptions
<1>tf. TranFinite  BY DEF MessageInterfaceAssumptions
<1>tt. TranTrans  BY DEF MessageInterfaceAssumptions
<1>ta. TranAcyclic  BY DEF MessageInterfaceAssumptions
<1>anp. AlwaysAProposal  BY DEF MessageInterfaceAssumptions
<1> DEFINE recs == {Digest(p) : p \in Refs(m)}
<1>rsub. Refs(m) \subseteq TranExclusive(m)  BY DEF Refs
<1>unf. Digest(m) = DigestR(m, recs)
  BY <1>tok, <1>tt, <1>tf, <1>ta, DigestRec
<1>ht. HighestTwoAsInvariant(m)  BY DigestInv DEF DigestInvariant
<1>htf. DigestHighestTwoAs(m) = HighestTwoAsAssemble(recs)
  BY <1>unf DEF DigestHighestTwoAs, DigestR
<1>htc. HighestTwoAsCorrect(m, HighestTwoAsAssemble(recs))
  <2>1. HighestTwoAsCorrect(m, DigestHighestTwoAs(m))
    BY <1>ht DEF HighestTwoAsInvariant, HighestTwoAsCorrect
  <2> QED BY <2>1, <1>htf
<1>fr. FreshAssemble(alpha, m, recs) <=> Fresh(alpha, m)
  BY <1>rsub, <1>htc,
     <1>tok, <1>tt, <1>tf, <1>ta, <1>anp, FreshResolve
<1>fa. DigestFresh(m)[alpha] <=> FreshAssemble(alpha, m, recs)
  <2>1. DigestFresh(m) = [al \in Learners |-> FreshAssemble(al, m, recs)]
    BY <1>unf DEF DigestFresh, DigestR
  <2> QED BY <2>1
<1> QED BY <1>fr, <1>fa
====================================================================
