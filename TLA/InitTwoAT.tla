------------------------------ MODULE InitTwoAT ------------------------------
EXTENDS HPaxosPlusCal, QuorumsHaveMembers

LEMMA InitTwoAT == LearnerGraphAssumptions /\ Init => TwoAInvariantT
<1> SUFFICES ASSUME LearnerGraphAssumptions, Init PROVE TwoAInvariantT  OBVIOUS
<1>lga. LearnersMightAgree /\ ValidLearnerGraphAssumption  BY DEF LearnerGraphAssumptions
<1>1. known_messages = [s \in SafeAcceptors |-> {}]  BY DEF Init
<1> SUFFICES ASSUME NEW s \in SafeAcceptors, NEW b \in Ballots, NEW alpha \in Learners,
                    NEW d \in (1..(MaxDepth(alpha))),
                    \A xx \in known_messages[s] : (IsProposal(xx) => B(xx) <= b),
                    SigS({xx \in known_messages[s] :
                          B(xx) = b /\ HasDepth(alpha, xx, d-1)}) \in Quorums(alpha)
             PROVE \E twoa \in Msgs :
                     B(twoa) = b /\ Sig(twoa) = s /\ HasDepth(alpha, twoa, d) /\ IsTwoA(twoa)
  BY DEF TwoAInvariantT
<1>2. known_messages[s] = {}  BY <1>1
<1>3. {xx \in known_messages[s] : B(xx) = b /\ HasDepth(alpha, xx, d-1)} = {}  BY <1>2
<1>4. SigS({}) = {}  BY DEF SigS
<1>5. SigS({xx \in known_messages[s] : B(xx) = b /\ HasDepth(alpha, xx, d-1)}) = {}
  BY <1>3, <1>4
<1>6. {} \in Quorums(alpha)  BY <1>5
<1>7. {} # {}  BY <1>lga, <1>6, QuorumsHaveMembers
<1> QED BY <1>7
====================================================================
