----------------------------- MODULE SafetyResolve -----------------------------
EXTENDS LearnerGraphConcrete, Fields, PairInCPairs

LEMMA SafetyResolve ==
  ASSUME LearnerGraphInterface = CLGI, NEW x \in 1..4, NEW y \in 1..4
  PROVE GetSpecifiedSafetySets({x,y}) =
        IF {x,y} \subseteq {1,2} THEN CLG ELSE IF {x,y} \subseteq {3,4} THEN CRG ELSE CCG
  <1>1. SpecifiedSafetySets = CSafety BY Fields
  <1>2. {x,y} \in CPairs BY PairInCPairs
  <1>3. {x,y} \in DOMAIN SpecifiedSafetySets BY <1>1, <1>2 DEF CSafety
  <1>4. GetSpecifiedSafetySets({x,y}) = CSafety[{x,y}] BY <1>1, <1>3 DEF GetSpecifiedSafetySets
  <1>5. CSafety[{x,y}] = IF {x,y} \subseteq {1,2} THEN CLG ELSE IF {x,y} \subseteq {3,4} THEN CRG ELSE CCG
    BY <1>2 DEF CSafety
  <1> QED BY <1>4, <1>5
=============================================================================
