----------------------------- MODULE CWellFormedRec -----------------------------
\* THE candidate-checking theorem: the digest-based WellFormedRec check an
\* acceptor runs on a received candidate record -- reading ONLY the digests
\* of its priors, never Tran -- is EQUIVALENT to CWellFormed of the record.
\* Conjunct by conjunct: (1) a proposal exists in the closure iff the
\* candidate is one or has a prior (CBAchievedByProposal at a prior); (2) the
\* assembled caught set IS CCaught(cand) (CaughtCand); (3) proposal/OneB/TwoA
\* via IsOneBU and LrnsU; (4) the assembled ballot IS CB(cand) (BalU).
\* Priors-canonicality is deliberately absent on both sides: it is not
\* digest-decidable, so CWellFormed does not demand it; safe acceptors
\* maintain it as an algorithm invariant instead (CSafeSentCanonical).
EXTENDS WellFormedRecDef, BalU, IsOneBU, LrnsU, CaughtCand,
        CBAchievedByProposal
LOCAL INSTANCE TLAPS

THEOREM CWellFormedRec ==
  ASSUME MessageInterfaceAssumptions,
         LearnersMightAgree, ValidLearnerGraphAssumption,
         MessageInterface = CMI,
         NEW sdr \in CSenders, NEW pl \in CPayload,
         NEW pr, pr \subseteq CMessages, IsFiniteSet(pr)
  PROVE LET cand == [sender |-> sdr, payload |-> pl, priors |-> pr]
        IN WellFormedRec(cand) <=> CWellFormed(cand)
<1>tok. TypeOKMessageInterface  BY DEF MessageInterfaceAssumptions
<1>tf. TranFinite  BY DEF MessageInterfaceAssumptions
<1>tt. TranTrans  BY DEF MessageInterfaceAssumptions
<1>ta. TranAcyclic  BY DEF MessageInterfaceAssumptions
<1>anp. AlwaysAProposal  BY DEF MessageInterfaceAssumptions
<1> DEFINE cand == [sender |-> sdr, payload |-> pl, priors |-> pr]
<1> DEFINE r    == {Digest(p) : p \in pr}
<1> DEFINE U    == UNION {CTran(p) : p \in pr}
<1>tr. CTran(cand) = {cand} \cup U /\ CTranExcl(cand) = U
  BY CBuiltTran
<1>flds. cand.sender = sdr /\ cand.payload = pl /\ cand.priors = pr
  OBVIOUS
<1>cprop. CIsProposal(cand) <=> pl \in CProposal  BY DEF CIsProposal
<1>csig. CSig(cand) = sdr  BY DEF CSig
<1>runf. WellFormedRec(cand) <=>
   (/\ CIsProposal(cand) \/ pr # {}
    /\ sdr \in Acceptors => sdr \notin CaughtAssemble(r)
    /\ CIsProposal(cand) \/ WFRIsOneB(pl, r) \/ WFRIsTwoA(sdr, pl, r)
    /\ CIsProposal(cand) => WFRBal(pl, r) = pl.ballot)
  BY <1>flds DEF WellFormedRec
<1>cunf. CWellFormed(cand) <=>
   (/\ \E a \in CTran(cand) : CIsProposal(a)
    /\ CSig(cand) \in Acceptors => CSig(cand) \notin CCaught(cand)
    /\ CIsProposal(cand) \/ CIsOneB(cand) \/ CIsTwoA(cand)
    /\ (CIsProposal(cand) => CB(cand) = pl.ballot))
  BY <1>flds DEF CWellFormed, CFilterOut
<1>c2eq. (sdr \in Acceptors => sdr \notin CaughtAssemble(r))
           <=> (CSig(cand) \in Acceptors => CSig(cand) \notin CCaught(cand))
  <2>1. CaughtAssemble(r) = CCaught(cand)
    BY <1>tok, <1>tt, <1>tf, <1>ta, CaughtCand
  <2> QED BY <2>1, <1>csig
<1>c1eq. (\E a \in CTran(cand) : CIsProposal(a))
           <=> (CIsProposal(cand) \/ pr # {})
  <2>fwd. (\E a \in CTran(cand) : CIsProposal(a))
            => (CIsProposal(cand) \/ pr # {})
    <3>1. CASE \E a \in CTran(cand) : CIsProposal(a)
      <4>a. PICK a \in CTran(cand) : CIsProposal(a)  BY <3>1
      <4>1. a \in {cand} \cup U  BY <1>tr
      <4>b. CASE a = cand
        <5> QED BY <4>a, <4>b
      <4>c. CASE a \in U
        <5>1. PICK p \in pr : a \in CTran(p)  BY <4>c
        <5> QED BY <5>1
      <4> QED BY <4>1, <4>b, <4>c
    <3> QED BY <3>1
  <2>bwd. (CIsProposal(cand) \/ pr # {})
            => (\E a \in CTran(cand) : CIsProposal(a))
    <3>a. CASE CIsProposal(cand)
      <4>1. cand \in CTran(cand)  BY <1>tr
      <4> QED BY <4>1, <3>a
    <3>b. CASE pr # {}
      <4>1. PICK p \in pr : TRUE  BY <3>b
      <4>2. PICK q \in CTran(p) : CIsProposal(q) /\ q.payload.ballot = CB(p)
        BY CBAchievedByProposal
      <4>3. q \in U  BY <4>2
      <4>4. q \in CTran(cand)  BY <4>3, <1>tr
      <4> QED BY <4>2, <4>4
    <3> QED BY <3>a, <3>b
  <2> QED BY <2>fwd, <2>bwd
<1>caseA. CASE ~(pl \in CProposal \/ pr # {})
  <2>w. ~WellFormedRec(cand)  BY <1>caseA, <1>runf, <1>cprop
  <2>u0. U = {}  BY <1>caseA
  <2>c. ~CWellFormed(cand)
    <3>1. CASE CWellFormed(cand)
      <4>1. PICK a \in CTran(cand) : CIsProposal(a)  BY <3>1, <1>cunf
      <4>2. a \in {cand} \cup U  BY <1>tr
      <4>3. a = cand  BY <4>2, <2>u0
      <4>4. CIsProposal(cand)  BY <4>1, <4>3
      <4> QED BY <4>4, <1>cprop, <1>caseA
    <3> QED BY <3>1
  <2> QED BY <2>w, <2>c
<1>caseB. CASE pl \in CProposal \/ pr # {}
  <2>bal. CB(cand) = WFRBal(pl, r)
    BY <1>tok, <1>tt, <1>tf, <1>ta, <1>anp, <1>caseB, BalU
  <2>oneb. CIsOneB(cand) <=> WFRIsOneB(pl, r)
    BY <1>caseB, IsOneBU
  <2>lrns. /\ WFRLrns(sdr, pl, r) \subseteq Learners
           /\ \A alpha \in Learners :
                CHasDepth(alpha, cand, 1) <=> alpha \in WFRLrns(sdr, pl, r)
    BY <1>caseB, LrnsU
  <2>twoa. CIsTwoA(cand) <=> WFRIsTwoA(sdr, pl, r)
    <3>1. CIsTwoA(cand)
            <=> (~CIsProposal(cand)
                 /\ \E alpha \in Learners : CHasDepth(alpha, cand, 1))
      BY DEF CIsTwoA
    <3>2. WFRIsTwoA(sdr, pl, r)
            <=> (pl \notin CProposal /\ WFRLrns(sdr, pl, r) # {})
      BY DEF WFRIsTwoA
    <3>3. (\E alpha \in Learners : CHasDepth(alpha, cand, 1))
            <=> WFRLrns(sdr, pl, r) # {}
      <4>fwd. (\E alpha \in Learners : CHasDepth(alpha, cand, 1))
                => WFRLrns(sdr, pl, r) # {}
        <5>1. CASE \E alpha \in Learners : CHasDepth(alpha, cand, 1)
          <6>1. PICK alpha \in Learners : CHasDepth(alpha, cand, 1)  BY <5>1
          <6>2. alpha \in WFRLrns(sdr, pl, r)  BY <6>1, <2>lrns
          <6> QED BY <6>2
        <5> QED BY <5>1
      <4>bwd. WFRLrns(sdr, pl, r) # {}
                => (\E alpha \in Learners : CHasDepth(alpha, cand, 1))
        <5>1. CASE WFRLrns(sdr, pl, r) # {}
          <6>1. PICK alpha \in WFRLrns(sdr, pl, r) : TRUE  BY <5>1
          <6>2. alpha \in Learners  BY <6>1, <2>lrns
          <6>3. CHasDepth(alpha, cand, 1)  BY <6>1, <6>2, <2>lrns
          <6> QED BY <6>2, <6>3
        <5> QED BY <5>1
      <4> QED BY <4>fwd, <4>bwd
    <3> QED BY <3>1, <3>2, <3>3, <1>cprop
  <2>c4eq. (CIsProposal(cand) => WFRBal(pl, r) = pl.ballot)
             <=> (CIsProposal(cand) => CB(cand) = pl.ballot)
    BY <2>bal
  <2>fwd. WellFormedRec(cand) => CWellFormed(cand)
    <3>1. CASE WellFormedRec(cand)
      <4>w. /\ CIsProposal(cand) \/ pr # {}
            /\ sdr \in Acceptors => sdr \notin CaughtAssemble(r)
            /\ CIsProposal(cand) \/ WFRIsOneB(pl, r) \/ WFRIsTwoA(sdr, pl, r)
            /\ CIsProposal(cand) => WFRBal(pl, r) = pl.ballot
        BY <3>1, <1>runf
      <4>c1. \E a \in CTran(cand) : CIsProposal(a)  BY <4>w, <1>c1eq
      <4>c2. CSig(cand) \in Acceptors => CSig(cand) \notin CCaught(cand)
        BY <4>w, <1>c2eq
      <4>c3. CIsProposal(cand) \/ CIsOneB(cand) \/ CIsTwoA(cand)
        BY <4>w, <2>oneb, <2>twoa
      <4>c4. CIsProposal(cand) => CB(cand) = pl.ballot
        BY <4>w, <2>c4eq
      <4> QED BY <4>c1, <4>c2, <4>c3, <4>c4, <1>cunf
    <3> QED BY <3>1
  <2>bwd. CWellFormed(cand) => WellFormedRec(cand)
    <3>1. CASE CWellFormed(cand)
      <4>c. /\ \E a \in CTran(cand) : CIsProposal(a)
            /\ CSig(cand) \in Acceptors => CSig(cand) \notin CCaught(cand)
            /\ CIsProposal(cand) \/ CIsOneB(cand) \/ CIsTwoA(cand)
            /\ (CIsProposal(cand) => CB(cand) = pl.ballot)
        BY <3>1, <1>cunf
      <4>w1. CIsProposal(cand) \/ pr # {}  BY <4>c, <1>c1eq
      <4>w2. sdr \in Acceptors => sdr \notin CaughtAssemble(r)
        BY <4>c, <1>c2eq
      <4>w3. CIsProposal(cand) \/ WFRIsOneB(pl, r) \/ WFRIsTwoA(sdr, pl, r)
        BY <4>c, <2>oneb, <2>twoa
      <4>w4. CIsProposal(cand) => WFRBal(pl, r) = pl.ballot
        BY <4>c, <2>c4eq
      <4> QED BY <4>w1, <4>w2, <4>w3, <4>w4, <1>runf
    <3> QED BY <3>1
  <2> QED BY <2>fwd, <2>bwd
<1> QED BY <1>caseA, <1>caseB
=============================================================================
