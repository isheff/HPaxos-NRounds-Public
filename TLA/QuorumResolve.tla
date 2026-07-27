----------------------------- MODULE QuorumResolve -----------------------------
EXTENDS LearnerGraphConcrete, Fields

LEMMA QuorumResolve ==
  ASSUME LearnerGraphInterface = CLGI, NEW x \in 1..4
  PROVE GetSpecifiedQuorums(x) = IF x \in {1,2} THEN CLQ ELSE CRQ
  <1>1. SpecifiedQuorums = CQuorums BY Fields
  <1>2. x \in DOMAIN SpecifiedQuorums BY <1>1 DEF CQuorums, CLrn
  <1>3. GetSpecifiedQuorums(x) = CQuorums[x] BY <1>1, <1>2 DEF GetSpecifiedQuorums
  <1>4. CQuorums[x] = IF x \in {1,2} THEN CLQ ELSE CRQ BY DEF CQuorums, CLrn
  <1> QED BY <1>3, <1>4
=============================================================================
