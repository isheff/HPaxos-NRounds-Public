------------------ MODULE MessageConcreteSupportsAssumptions ------------------
EXTENDS MessageConcrete, CTypeOKMessageInterface, CTranFinite, CTranTransProof,
        CTranAcyclic, CAlwaysAProposal, CAlwaysANewProposal, CAlwaysANewOneB,
        CAlwaysANewTwoA, CAcceptorsSubsetSenders

\* ===================================================================
\* Capstone: the concrete instantiation CMI satisfies ALL of
\* MessageInterfaceAssumptions, given only the ValueInterface assumptions
\* (implicit) and the two LearnerGraph assumptions that make quorums nonempty.
\* ===================================================================
THEOREM MessageConcreteSupportsAssumptions ==
  ASSUME MessageInterface = CMI, LearnersMightAgree, ValidLearnerGraphAssumption
  PROVE MessageInterfaceAssumptions
<1>1. TypeOKMessageInterface  BY CTypeOKMessageInterface
<1>2. TranFinite  BY CTranFinite
<1>3. TranTrans  BY CTranTransProof
<1>4. TranAcyclic  BY CTranAcyclic
<1>5. AlwaysAProposal  BY CAlwaysAProposal
<1>6. AlwaysANewProposal  BY CAlwaysANewProposal
<1>7. AlwaysANewOneB  BY CAlwaysANewOneB
<1>8. AlwaysANewTwoA  BY CAlwaysANewTwoA
<1>9. AcceptorsSubsetSenders  BY CAcceptorsSubsetSenders
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9
  DEF MessageInterfaceAssumptions
=============================================================================
