---------------------------- MODULE MemoPCaughtCand ----------------------------
\* Concrete reading of MemoPCaughtU at the built candidate: the caught
\* assembly over the priors' MemoP records IS CCaught(cand).  The candidate
\* itself never contributes a witness pair -- everything in the closure is in
\* CTran(cand), so a pair involving cand fails the incomparability test --
\* hence CCaughtS over {cand} \cup U collapses to CCaughtS(U), which resolves
\* to the interface-side CaughtS(U) that MemoPCaughtU computes.
EXTENDS MemoPCaughtU, CBuiltTran, CUnionTranFiniteClosed, CCaughtSResolve,
        CTranResolve, CFields
LOCAL INSTANCE TLAPS

LEMMA MemoPCaughtCand ==
  ASSUME MessageInterfaceAssumptions,
         LearnersMightAgree, ValidLearnerGraphAssumption,
         MessageInterface = CMI,
         NEW sdr \in CSenders, NEW pl \in CPayload,
         NEW pr, pr \subseteq CMessages, IsFiniteSet(pr)
  PROVE LET cand == [sender |-> sdr, payload |-> pl, priors |-> pr]
            r    == {MemoP(p) : p \in pr}
        IN CaughtAssemble(r) = CCaught(cand)
<1> DEFINE cand == [sender |-> sdr, payload |-> pl, priors |-> pr]
<1> DEFINE r    == {MemoP(p) : p \in pr}
<1> DEFINE U    == UNION {CTran(p) : p \in pr}
<1> DEFINE UI   == UNION {Tran(p) : p \in pr}
<1>tok. TypeOKMessageInterface  BY DEF MessageInterfaceAssumptions
<1>tf. TranFinite  BY DEF MessageInterfaceAssumptions
<1>tt. TranTrans  BY DEF MessageInterfaceAssumptions
<1>ta. TranAcyclic  BY DEF MessageInterfaceAssumptions
<1>msub. pr \subseteq Messages  BY CFields
<1>ueq. UI = U
  <2>1. \A p \in pr : Tran(p) = CTran(p)  BY CTranResolve
  <2>sub. UI \subseteq U
    <3> SUFFICES ASSUME NEW z \in UI PROVE z \in U  OBVIOUS
    <3>1. PICK p \in pr : z \in Tran(p)  OBVIOUS
    <3> QED BY <3>1, <2>1
  <2>sup. U \subseteq UI
    <3> SUFFICES ASSUME NEW z \in U PROVE z \in UI  OBVIOUS
    <3>1. PICK p \in pr : z \in CTran(p)  OBVIOUS
    <3> QED BY <3>1, <2>1
  <2> QED BY <2>sub, <2>sup
<1>1. CaughtAssemble(r) = CaughtS(UI)  BY MemoPCaughtU
<1>2. CaughtS(UI) = CaughtS(U)  BY <1>ueq
<1>usub. U \subseteq CMessages  BY CUnionTranFiniteClosed
<1>3. CaughtS(U) = CCaughtS(U)  BY <1>usub, CCaughtSResolve
<1>tr. CTran(cand) = {cand} \cup U /\ CTranExcl(cand) = U  BY CBuiltTran
<1>4. CCaughtS({cand} \cup U) = CCaughtS(U)
  <2>sup. CCaughtS(U) \subseteq CCaughtS({cand} \cup U)
    <3> SUFFICES ASSUME NEW a \in CCaughtS(U)
        PROVE a \in CCaughtS({cand} \cup U)  OBVIOUS
    <3>1. PICK m1 \in U, m2 \in U :
            /\ CSig(m1) = a /\ CSig(m2) = a
            /\ m1 \notin CTran(m2) /\ m2 \notin CTran(m1)
      BY DEF CCaughtS
    <3>2. a \in Acceptors  BY DEF CCaughtS
    <3> QED BY <3>1, <3>2 DEF CCaughtS
  <2>sub. CCaughtS({cand} \cup U) \subseteq CCaughtS(U)
    <3> SUFFICES ASSUME NEW a \in CCaughtS({cand} \cup U)
        PROVE a \in CCaughtS(U)  OBVIOUS
    <3>1. PICK m1 \in {cand} \cup U : \E m2 \in {cand} \cup U :
            /\ CSig(m1) = a /\ CSig(m2) = a
            /\ m1 \notin CTran(m2) /\ m2 \notin CTran(m1)
      BY DEF CCaughtS
    <3>2. PICK m2 \in {cand} \cup U :
            /\ CSig(m1) = a /\ CSig(m2) = a
            /\ m1 \notin CTran(m2) /\ m2 \notin CTran(m1)
      BY <3>1
    <3>3. a \in Acceptors  BY DEF CCaughtS
    <3>m1. m1 # cand
      <4>1. CASE m1 = cand
        <5>1. m2 \in CTran(m1)  BY <4>1, <1>tr
        <5> QED BY <5>1, <3>2
      <4> QED BY <4>1
    <3>m2. m2 # cand
      <4>1. CASE m2 = cand
        <5>1. m1 \in CTran(m2)  BY <4>1, <1>tr
        <5> QED BY <5>1, <3>2
      <4> QED BY <4>1
    <3>4. m1 \in U /\ m2 \in U  BY <3>m1, <3>m2
    <3> QED BY <3>2, <3>3, <3>4 DEF CCaughtS
  <2> QED BY <2>sub, <2>sup
<1>5. CCaught(cand) = CCaughtS(CTran(cand))  BY DEF CCaught
<1>6. CCaughtS(CTran(cand)) = CCaughtS({cand} \cup U)  BY <1>tr
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6
=============================================================================
