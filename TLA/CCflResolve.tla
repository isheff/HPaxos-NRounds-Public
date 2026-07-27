------------------------------ MODULE CCflResolve ------------------------------
EXTENDS MessageConcrete, CMinLevelDom, CMessagesSubMC, CFields,
        CTypeOKMessageInterface, CTranTransProof, CTranFinite, CTranAcyclic,
        CCflRec, CTranResolve, CMessageTranClosed, CTranExclDecreasesLevel,
        CCflId, CBResolve, CSigResolve, CIsOneBResolve, CQdSubset,
        CSigSResolve, CVResolve, CConResolve,
        RecursiveMessageTranFuncRec, NaturalsInduction
LOCAL INSTANCE TLAPS

\* the big bridge: CombinedFreshQdLrnsId (abstract) = CCfl (concrete) on CMessages
LEMMA CCflResolve ==
  ASSUME MessageInterface = CMI
  PROVE \A x \in CMessages : CombinedFreshQdLrnsId(x) = CCfl(x)
<1> DEFINE Q(n) == \A x \in CMessages : CMinLevel(x) = n => CombinedFreshQdLrnsId(x) = CCfl(x)
<1> SUFFICES \A n \in Nat : Q(n)
  BY CMinLevelDom, CMessagesSubMC DEF Q
<1> HIDE DEF Q
<1>ind. \A n \in Nat : (\A k \in 0..(n-1) : Q(k)) => Q(n)
  <2> USE DEF Q
  <2> SUFFICES ASSUME NEW n \in Nat, \A k \in 0..(n-1) : Q(k),
                      NEW x \in CMessages, CMinLevel(x) = n
               PROVE CombinedFreshQdLrnsId(x) = CCfl(x)
    OBVIOUS
  <2>xmc. x \in CMC  BY CMessagesSubMC
  <2>xM. x \in Messages  BY CFields
  <2>tok. TypeOKMessageInterface  BY CTypeOKMessageInterface
  <2>ttr. TranTrans  BY CTranTransProof
  <2>tfin. TranFinite  BY CTranFinite
  <2>tac. TranAcyclic  BY CTranAcyclic
  <2>abs. CombinedFreshQdLrnsId(x) =
            CombinedFreshQdLrnsIdR(x, {CombinedFreshQdLrnsId(p) : p \in TranExclusive(x)})
    BY <2>xM, <2>tok, <2>ttr, <2>tfin, <2>tac, RecursiveMessageTranFuncRec
    DEF CombinedFreshQdLrnsId
  <2>conc. CCfl(x) = CCflR(x, {CCfl(p) : p \in CTranExcl(x)})  BY <2>xmc, CCflRec
  <2>teEq. TranExclusive(x) = CTranExcl(x)
    <3>1. Tran(x) = CTran(x)  BY CTranResolve
    <3> QED BY <3>1 DEF TranExclusive, CTranExcl
  <2>childMC. \A p \in CTranExcl(x) : p \in CMessages
    <3> SUFFICES ASSUME NEW p \in CTranExcl(x) PROVE p \in CMessages  OBVIOUS
    <3>1. p \in CTran(x)  BY DEF CTranExcl
    <3> QED BY <3>1, CMessageTranClosed
  <2>indHyp. \A p \in CTranExcl(x) : CombinedFreshQdLrnsId(p) = CCfl(p)
    <3> SUFFICES ASSUME NEW p \in CTranExcl(x) PROVE CombinedFreshQdLrnsId(p) = CCfl(p)  OBVIOUS
    <3>1. p \in CMessages  BY <2>childMC
    <3>2. p \in CMC  BY <3>1, CMessagesSubMC
    <3>3. CMinLevel(p) < CMinLevel(x)  BY <2>xmc, CTranExclDecreasesLevel
    <3>4. CMinLevel(p) \in Nat  BY <3>2, CMinLevelDom
    <3>5. CMinLevel(p) \in 0..(n-1)  BY <3>3, <3>4
    <3> QED BY <3>1, <3>5
  <2>setsEq. {CombinedFreshQdLrnsId(p) : p \in TranExclusive(x)} = {CCfl(p) : p \in CTranExcl(x)}
    BY <2>teEq, <2>indHyp
  <2> DEFINE r == {CCfl(p) : p \in CTranExcl(x)}
  <2>rchild. \A mm \in r : mm.id \in CTranExcl(x) /\ mm = CCfl(mm.id)
    <3> SUFFICES ASSUME NEW mm \in r PROVE mm.id \in CTranExcl(x) /\ mm = CCfl(mm.id)  OBVIOUS
    <3>a. PICK p \in CTranExcl(x) : mm = CCfl(p)  OBVIOUS
    <3>b. p \in CMC  BY <2>childMC, <3>a, CMessagesSubMC
    <3>c. CCfl(p).id = p  BY <3>b, CCflId
    <3> QED BY <3>a, <3>c
  <2> DEFINE qdxA == [pr \in Learners \X Nat |->
       LET al == pr[1]  dl == pr[2]
       IN {yy.id: yy \in {mm \in r:
             /\ dl > 0
             /\ B(mm.id) = B(x)
             /\ Sig(mm.id) \in Acceptors
             /\ dl = 1 => (IsOneB(mm.id) /\ mm.fresh[al])
             /\ dl > 1 => SigS(mm.qd[<<al, dl-1>>]) \in Quorums(al)}}]
  <2> DEFINE qdxC == [pr \in Learners \X Nat |->
       LET al == pr[1]  dl == pr[2]
       IN {yy.id: yy \in {mm \in r:
             /\ dl > 0
             /\ CB(mm.id) = CB(x)
             /\ CSig(mm.id) \in Acceptors
             /\ dl = 1 => (CIsOneB(mm.id) /\ mm.fresh[al])
             /\ dl > 1 => CSigS(mm.qd[<<al, dl-1>>]) \in Quorums(al)}}]
  <2>filterEq. \A al \in Learners, dl \in Nat :
      {mm \in r: /\ dl>0 /\ B(mm.id)=B(x) /\ Sig(mm.id) \in Acceptors /\ (dl=1=>(IsOneB(mm.id)/\mm.fresh[al]))
                 /\ (dl>1=>SigS(mm.qd[<<al,dl-1>>]) \in Quorums(al))}
    = {mm \in r: /\ dl>0 /\ CB(mm.id)=CB(x) /\ CSig(mm.id) \in Acceptors /\ (dl=1=>(CIsOneB(mm.id)/\mm.fresh[al]))
                 /\ (dl>1=>CSigS(mm.qd[<<al,dl-1>>]) \in Quorums(al))}
    <3> SUFFICES ASSUME NEW al \in Learners, NEW dl \in Nat, NEW mm \in r
                 PROVE (/\ dl>0 /\ B(mm.id)=B(x) /\ Sig(mm.id) \in Acceptors /\ (dl=1=>(IsOneB(mm.id)/\mm.fresh[al]))
                        /\ (dl>1=>SigS(mm.qd[<<al,dl-1>>]) \in Quorums(al)))
                    <=> (/\ dl>0 /\ CB(mm.id)=CB(x) /\ CSig(mm.id) \in Acceptors /\ (dl=1=>(CIsOneB(mm.id)/\mm.fresh[al]))
                        /\ (dl>1=>CSigS(mm.qd[<<al,dl-1>>]) \in Quorums(al)))
      OBVIOUS
    <3>pid. mm.id \in CTranExcl(x)  BY <2>rchild
    <3>pmc. mm.id \in CMessages  BY <3>pid, <2>childMC
    <3>bres. B(mm.id) = CB(mm.id)  BY <3>pmc, CBResolve
    <3>bxres. B(x) = CB(x)  BY CBResolve
    <3>sigacc. Sig(mm.id) = CSig(mm.id)  BY <3>pmc, CSigResolve
    <3>oneb. IsOneB(mm.id) = CIsOneB(mm.id)  BY <3>pmc, CIsOneBResolve
    <3>sigres. dl > 1 => SigS(mm.qd[<<al,dl-1>>]) = CSigS(mm.qd[<<al,dl-1>>])
      <4> SUFFICES ASSUME dl > 1 PROVE SigS(mm.qd[<<al,dl-1>>]) = CSigS(mm.qd[<<al,dl-1>>])
        OBVIOUS
      <4>nat. dl - 1 \in Nat  OBVIOUS
      <4>qdsub. mm.qd[<<al, dl-1>>] \subseteq CMessages
        <5>1. mm = CCfl(mm.id)  BY <2>rchild
        <5>2. mm.id \in CMC  BY <3>pmc, CMessagesSubMC
        <5>3. CCfl(mm.id).qd[<<al, dl-1>>] \subseteq CTranExcl(mm.id)  BY <5>2, <4>nat, CQdSubset
        <5>4. CTranExcl(mm.id) \subseteq CMessages
          <6> SUFFICES ASSUME NEW z \in CTranExcl(mm.id) PROVE z \in CMessages  OBVIOUS
          <6>1. z \in CTran(mm.id)  BY DEF CTranExcl
          <6> QED BY <6>1, <3>pmc, CMessageTranClosed
        <5> QED BY <5>1, <5>3, <5>4
      <4> QED BY <4>qdsub, CSigSResolve
    <3> QED BY <3>bres, <3>bxres, <3>sigacc, <3>oneb, <3>sigres
  <2>qdxptwise. \A al \in Learners, dl \in Nat : qdxA[<<al,dl>>] = qdxC[<<al,dl>>]
    <3> SUFFICES ASSUME NEW al \in Learners, NEW dl \in Nat PROVE qdxA[<<al,dl>>] = qdxC[<<al,dl>>]
      OBVIOUS
    <3>dom. <<al,dl>> \in Learners \X Nat  OBVIOUS
    <3>a. qdxA[<<al,dl>>] = {yy.id: yy \in {mm \in r:
             /\ dl > 0
             /\ B(mm.id) = B(x)
             /\ Sig(mm.id) \in Acceptors
             /\ dl = 1 => (IsOneB(mm.id) /\ mm.fresh[al])
             /\ dl > 1 => SigS(mm.qd[<<al, dl-1>>]) \in Quorums(al)}}
      BY <3>dom
    <3>c. qdxC[<<al,dl>>] = {yy.id: yy \in {mm \in r:
             /\ dl > 0
             /\ CB(mm.id) = CB(x)
             /\ CSig(mm.id) \in Acceptors
             /\ dl = 1 => (CIsOneB(mm.id) /\ mm.fresh[al])
             /\ dl > 1 => CSigS(mm.qd[<<al, dl-1>>]) \in Quorums(al)}}
      BY <3>dom
    <3>seteq. {mm \in r:
             /\ dl > 0
             /\ B(mm.id) = B(x)
             /\ Sig(mm.id) \in Acceptors
             /\ dl = 1 => (IsOneB(mm.id) /\ mm.fresh[al])
             /\ dl > 1 => SigS(mm.qd[<<al, dl-1>>]) \in Quorums(al)}
           = {mm \in r:
             /\ dl > 0
             /\ CB(mm.id) = CB(x)
             /\ CSig(mm.id) \in Acceptors
             /\ dl = 1 => (CIsOneB(mm.id) /\ mm.fresh[al])
             /\ dl > 1 => CSigS(mm.qd[<<al, dl-1>>]) \in Quorums(al)}
      \* keep r opaque: this is a pure instantiation of <2>filterEq, and
      \* unfolding r (= {CCfl(p) : ...}) blows the obligation past what the
      \* backends absorb
      <4> HIDE DEF r
      <4> QED BY <2>filterEq
    <3> QED BY <3>a, <3>c, <3>seteq
  <2>qdxEq. qdxA = qdxC
    <3> SUFFICES ASSUME NEW pr \in Learners \X Nat PROVE qdxA[pr] = qdxC[pr]
      OBVIOUS
    <3>1. pr = <<pr[1], pr[2]>> /\ pr[1] \in Learners /\ pr[2] \in Nat  OBVIOUS
    <3> QED BY <3>1, <2>qdxptwise
  <2>qdxAsub. \A al \in Learners, dl \in Nat : qdxA[<<al,dl>>] \subseteq CMessages
    <3> SUFFICES ASSUME NEW al \in Learners, NEW dl \in Nat, NEW ee \in qdxA[<<al,dl>>]
                 PROVE ee \in CMessages
      OBVIOUS
    <3>1. PICK mm \in r : ee = mm.id  OBVIOUS
    <3> QED BY <3>1, <2>rchild, <2>childMC
  <2>lrnsA. [al2 \in Learners |-> Sig(x) \in Acceptors /\ SigS(qdxA[<<al2,1>>]) \in Quorums(al2)]
          = [al2 \in Learners |-> CSig(x) \in Acceptors /\ CSigS(qdxC[<<al2,1>>]) \in Quorums(al2)]
    <3> SUFFICES ASSUME NEW al2 \in Learners
                 PROVE (Sig(x) \in Acceptors /\ SigS(qdxA[<<al2,1>>]) \in Quorums(al2))
                   <=> (CSig(x) \in Acceptors /\ CSigS(qdxC[<<al2,1>>]) \in Quorums(al2))
      OBVIOUS
    <3>sx. Sig(x) = CSig(x)  BY CSigResolve
    <3>1. qdxA[<<al2,1>>] \subseteq CMessages  BY <2>qdxAsub
    <3>2. SigS(qdxA[<<al2,1>>]) = CSigS(qdxA[<<al2,1>>])  BY <3>1, CSigSResolve
    <3> QED BY <3>sx, <3>2, <2>qdxEq
  <2>freshA. [al2 \in Learners |->
        \A mm \in r : \/ V(mm.id) = V(x)
                      \/ Con(al2, x) \cap mm.lrns = {}
                      \/ \E pp \in r : B(pp.id) > B(mm.id) /\ Con(al2, x) \cap pp.lrns # {}]
      = [al2 \in Learners |->
        \A mm \in r : \/ CV(mm.id) = CV(x)
                      \/ CCon(al2, x) \cap mm.lrns = {}
                      \/ \E pp \in r : CB(pp.id) > CB(mm.id) /\ CCon(al2, x) \cap pp.lrns # {}]
    <3> SUFFICES ASSUME NEW al2 \in Learners
                 PROVE (\A mm \in r : \/ V(mm.id) = V(x)
                                       \/ Con(al2, x) \cap mm.lrns = {}
                                       \/ \E pp \in r : B(pp.id) > B(mm.id) /\ Con(al2, x) \cap pp.lrns # {})
                    <=> (\A mm \in r : \/ CV(mm.id) = CV(x)
                                       \/ CCon(al2, x) \cap mm.lrns = {}
                                       \/ \E pp \in r : CB(pp.id) > CB(mm.id) /\ CCon(al2, x) \cap pp.lrns # {})
      OBVIOUS
    <3>vx. V(x) = CV(x)  BY CVResolve
    <3>conx. Con(al2, x) = CCon(al2, x)  BY CConResolve
    <3>each. \A mm \in r :
        (V(mm.id) = V(x) <=> CV(mm.id) = CV(x))
      <4> SUFFICES ASSUME NEW mm \in r PROVE V(mm.id) = V(x) <=> CV(mm.id) = CV(x)
        OBVIOUS
      <4>a. mm.id \in CMessages  BY <2>rchild, <2>childMC
      <4>b. V(mm.id) = CV(mm.id)  BY <4>a, CVResolve
      <4> QED BY <4>b, <3>vx
    <3>each2. \A mm \in r, pp \in r :
        (B(pp.id) > B(mm.id) <=> CB(pp.id) > CB(mm.id))
      <4> SUFFICES ASSUME NEW mm \in r, NEW pp \in r
                   PROVE B(pp.id) > B(mm.id) <=> CB(pp.id) > CB(mm.id)
        OBVIOUS
      <4>a. mm.id \in CMessages /\ pp.id \in CMessages  BY <2>rchild, <2>childMC
      <4>b. B(mm.id) = CB(mm.id) /\ B(pp.id) = CB(pp.id)  BY <4>a, CBResolve
      <4> QED BY <4>b
    <3> QED BY <3>each, <3>each2, <3>conx
  <2>Fapply. CombinedFreshQdLrnsIdR(x, r) = CCflR(x, r)
    BY <2>qdxEq, <2>lrnsA, <2>freshA DEF CombinedFreshQdLrnsIdR, CCflR
  <2> QED BY <2>abs, <2>conc, <2>setsEq, <2>Fapply
<1> QED BY <1>ind, GeneralNatInduction, IsaM("blast")
=============================================================================
