------------------------------ MODULE MemoPCaughtU ------------------------------
\* The (pr, U)-virtualized MemoPCaughtStep: for a FINITE prior set pr of real
\* messages, the caught assembly over the priors' MemoP records equals
\* CaughtS(UU) for UU := UNION {Tran(p) : p \in pr} -- the closure a
\* candidate with those priors would have.
\*
\* This is CaughtU with the canonical memos replaced by MemoP records: the
\* chain test reads the P-chains, and every chain property it needs comes
\* from MemoPGoodInv (the priors, and everything in UU, are real messages),
\* with MemoPDKU for the assembled deepestknown map and MemoPDKMaximalU for
\* the "strictly above the entry" case.
EXTENDS MemoPUDefs, MemoPDefs, MemoPGoodInv, MemoPDKU, MemoPDKMaximalU,
        DeepestKnownInv, TranSubMessages, CFields, CMessageTranClosed,
        CTranResolve
LOCAL INSTANCE TLAPS

LEMMA MemoPCaughtU ==
  ASSUME MessageInterfaceAssumptions,
         LearnersMightAgree, ValidLearnerGraphAssumption,
         MessageInterface = CMI,
         NEW pr, pr \subseteq CMessages, IsFiniteSet(pr)
  PROVE CaughtAssemble({MemoP(p) : p \in pr})
          = CaughtS(UNION {Tran(p) : p \in pr})
<1> DEFINE rP == {MemoP(q) : q \in pr}
<1> DEFINE caA == CaughtAssemble(rP)
<1> DEFINE dkA == DeepestKnownAssemble(rP)
<1> DEFINE UU == UNION {Tran(p) : p \in pr}
<1> DEFINE Test == {y \in CaughtCandidates(rP) :
                      /\ Sig(y) \in Acceptors
                      /\ y \notin DeepestKnownAssemble(rP)[Sig(y)][2].prevtran}
<1> HIDE DEF Test
\* ------------------------------------------------------------------ prelude
<1>tok. TypeOKMessageInterface  BY DEF MessageInterfaceAssumptions
<1>tf. TranFinite  BY DEF MessageInterfaceAssumptions
<1>tt. TranTrans  BY DEF MessageInterfaceAssumptions
<1>ta. TranAcyclic  BY DEF MessageInterfaceAssumptions
<1>anp. AlwaysAProposal  BY DEF MessageInterfaceAssumptions
<1>prMsg. pr \subseteq Messages  BY CFields
<1>texP. \A q \in pr : Tran(q) \subseteq UU  OBVIOUS
<1>texPP. \A q \in pr : TranExclusive(q) \subseteq UU
  BY <1>texP DEF TranExclusive
<1>pTE. \A q \in pr : q \in UU
  <2> SUFFICES ASSUME NEW q \in pr PROVE q \in UU  OBVIOUS
  <2>1. q \in Tran(q)  BY DEF Tran
  <2> QED BY <2>1
<1>teM. UU \subseteq Messages
  <2> SUFFICES ASSUME NEW z \in UU PROVE z \in Messages  OBVIOUS
  <2>1. PICK q \in pr : z \in Tran(q)  OBVIOUS
  <2>2. q \in Messages  BY <1>prMsg
  <2> QED BY <2>1, <2>2, <1>tok, TranSubMessages
<1>uCM. UU \subseteq CMessages
  <2> SUFFICES ASSUME NEW z \in UU PROVE z \in CMessages  OBVIOUS
  <2>1. PICK q \in pr : z \in Tran(q)  OBVIOUS
  <2>2. Tran(q) = CTran(q)  BY CTranResolve
  <2> QED BY <2>1, <2>2, CMessageTranClosed
<1>ucl. \A z \in UU : Tran(z) \subseteq UU
  <2> SUFFICES ASSUME NEW z \in UU PROVE Tran(z) \subseteq UU  OBVIOUS
  <2>1. PICK q \in pr : z \in Tran(q)  OBVIOUS
  <2>2. Tran(z) \subseteq Tran(q)  BY <2>1, <1>prMsg, <1>tt DEF TranTrans
  <2> QED BY <2>2, <1>texP
<1>ihU. \A z \in UU : MemoPGood(z)  BY <1>uCM, MemoPGoodInv
<1>ihq. \A q \in pr : MemoPGood(q)  BY MemoPGoodInv
<1>idp. \A q \in pr : /\ MemoP(q).id = q
                      /\ MemoP(q).caught = Caught(q)
  BY <1>ihq DEF MemoPGood
<1>ihdkP. \A q \in pr : DeepestKnownCorrectP(q, MemoP(q).deepestknown)
  BY <1>ihq DEF MemoPGood
<1>invA. DeepestKnownCorrectUP(UU, dkA)  BY MemoPDKU
<1>dom. DOMAIN dkA = SigS(UU)
  BY <1>invA DEF DeepestKnownCorrectUP
<1>ca. caA = (UNION {rc.caught : rc \in rP}) \cup SigS(Test)
  BY DEF CaughtAssemble, Test
<1>pt. \A s \in DOMAIN dkA :
         DeepestKnownAssemble(rP)[s][2].prevtran
           = MemoP(dkA[s][2].id).prevtran
  <2> SUFFICES ASSUME NEW s \in DOMAIN dkA
      PROVE DeepestKnownAssemble(rP)[s][2].prevtran
              = MemoP(dkA[s][2].id).prevtran
    OBVIOUS
  <2>can. dkA[s][2] = MemoP(dkA[s][2].id)
    BY <1>invA DEF DeepestKnownCorrectUP
  <2> QED BY <2>can
\* --------------------------------------------------------------- candidates
<1>candTE. \A y \in CaughtCandidates(rP) : y \in UU
  <2> SUFFICES ASSUME NEW y \in CaughtCandidates(rP)
      PROVE y \in UU
    OBVIOUS
  <2>split. \/ y \in {rc.id : rc \in rP}
            \/ y \in UNION {MemoDKMessages(rc) : rc \in rP}
    BY DEF CaughtCandidates
  <2>a. CASE y \in {rc.id : rc \in rP}
    <3>1. PICK rc \in rP : y = rc.id  BY <2>a
    <3>2. PICK q \in pr : rc = MemoP(q)  BY <3>1
    <3>3. y = q  BY <3>1, <3>2, <1>idp
    <3> QED BY <3>3, <1>pTE
  <2>b. CASE y \in UNION {MemoDKMessages(rc) : rc \in rP}
    <3>1. PICK rc \in rP : y \in MemoDKMessages(rc)  BY <2>b
    <3>2. PICK q \in pr : rc = MemoP(q)  BY <3>1
    <3>3. PICK s \in DOMAIN MemoP(q).deepestknown :
            y = MemoP(q).deepestknown[s][2].id
      BY <3>1, <3>2 DEF MemoDKMessages
    <3>4. y \in TranExclusive(q)
      BY <3>3, <1>ihdkP DEF DeepestKnownCorrectP
    <3> QED BY <3>4, <1>texPP
  <2> QED BY <2>split, <2>a, <2>b
<1>candRef. \A q \in pr : q \in CaughtCandidates(rP)
  <2> SUFFICES ASSUME NEW q \in pr PROVE q \in CaughtCandidates(rP)  OBVIOUS
  <2>1. MemoP(q) \in rP  OBVIOUS
  <2>2. MemoP(q).id = q  BY <1>idp
  <2> QED BY <2>1, <2>2 DEF CaughtCandidates
<1>candDK. \A q \in pr : \A s \in DOMAIN MemoP(q).deepestknown :
             MemoP(q).deepestknown[s][2].id \in CaughtCandidates(rP)
  <2> SUFFICES ASSUME NEW q \in pr,
                      NEW s \in DOMAIN MemoP(q).deepestknown
      PROVE MemoP(q).deepestknown[s][2].id \in CaughtCandidates(rP)
    OBVIOUS
  <2>1. MemoP(q) \in rP  OBVIOUS
  <2>2. MemoP(q).deepestknown[s][2].id \in MemoDKMessages(MemoP(q))
    BY DEF MemoDKMessages
  <2> QED BY <2>1, <2>2 DEF CaughtCandidates
\* -------------------------------------------------------------- soundness
<1>sound. caA \subseteq CaughtS(UU)
  <2>refs. UNION {rc.caught : rc \in rP} \subseteq CaughtS(UU)
    <3> SUFFICES ASSUME NEW a \in UNION {rc.caught : rc \in rP}
        PROVE a \in CaughtS(UU)
      OBVIOUS
    <3>1. PICK rc \in rP : a \in rc.caught  OBVIOUS
    <3>2. PICK q \in pr : rc = MemoP(q)  BY <3>1
    <3>3. a \in Caught(q)  BY <3>1, <3>2, <1>idp
    <3>4. PICK m1 \in Tran(q), m2 \in Tran(q) :
            /\ Sig(m1) = a /\ Sig(m2) = a
            /\ m1 \notin Tran(m2) /\ m2 \notin Tran(m1)
      BY <3>3 DEF Caught, CaughtS
    <3>5. a \in Acceptors  BY <3>3 DEF Caught, CaughtS
    <3>6. m1 \in UU /\ m2 \in UU  BY <3>4, <1>texP
    <3> QED BY <3>4, <3>5, <3>6 DEF CaughtS
  <2>test. SigS(Test) \subseteq CaughtS(UU)
    <3> SUFFICES ASSUME NEW a \in SigS(Test) PROVE a \in CaughtS(UU)  OBVIOUS
    <3>y. PICK y \in Test : a = Sig(y)  BY DEF SigS
    <3>yc. y \in CaughtCandidates(rP) /\ Sig(y) \in Acceptors
             /\ y \notin DeepestKnownAssemble(rP)[Sig(y)][2].prevtran
      BY <3>y DEF Test
    <3>yTE. y \in UU  BY <3>yc, <1>candTE
    <3>sdom. Sig(y) \in DOMAIN dkA
      <4>1. Sig(y) \in SigS(UU)  BY <3>yTE DEF SigS
      <4> QED BY <4>1, <1>dom
    <3> DEFINE zs == dkA[Sig(y)][2].id
    <3>ynot. y \notin MemoP(zs).prevtran  BY <3>yc, <3>sdom, <1>pt
    <3>ze. zs \in UU /\ Sig(zs) = Sig(y)
      BY <1>invA, <3>sdom DEF DeepestKnownCorrectUP
    <3>zM. zs \in Messages  BY <3>ze, <1>teM
    <3>yM. y \in Messages  BY <3>yTE, <1>teM
    <3>ihz. MemoPGood(zs)  BY <3>ze, <1>ihU
    <3>yneq. y # zs
      <4>1. zs \in MemoP(zs).prevtran  BY <3>ihz DEF MemoPGood
      <4> QED BY <4>1, <3>ynot
    <3>c1. CASE y \in Tran(zs)
      <4>1. y \in TranExclusive(zs)  BY <3>c1, <3>yneq DEF TranExclusive
      <4>2. Sig(zs) \in Caught(zs)
        BY <4>1, <3>ynot, <3>ze, <3>yc, <3>ihz DEF MemoPGood
      <4>3. PICK m1 \in Tran(zs), m2 \in Tran(zs) :
              /\ Sig(m1) = Sig(zs) /\ Sig(m2) = Sig(zs)
              /\ m1 \notin Tran(m2) /\ m2 \notin Tran(m1)
        BY <4>2 DEF Caught, CaughtS
      <4>4. m1 \in UU /\ m2 \in UU  BY <4>3, <3>ze, <1>ucl
      <4> QED BY <4>3, <4>4, <3>ze, <3>y, <3>yc DEF CaughtS
    <3>c2. CASE zs \in Tran(y)
      <4>1. zs \in TranExclusive(y)  BY <3>c2, <3>yneq DEF TranExclusive
      <4> QED BY <4>1, <3>sdom, <3>yTE, <1>teM, <1>invA,
                   <1>tok, <1>tt, <1>tf, <1>ta, MemoPDKMaximalU
    <3>c3. CASE y \notin Tran(zs) /\ zs \notin Tran(y)
      <4>1. y \in UU /\ zs \in UU  BY <3>yTE, <3>ze
      <4> QED BY <3>c3, <4>1, <3>ze, <3>yc, <3>y DEF CaughtS
    <3> QED BY <3>c1, <3>c2, <3>c3
  <2> QED BY <1>ca, <2>refs, <2>test
\* ------------------------------------------------------------ completeness
<1>compl. CaughtS(UU) \subseteq caA
  <2> SUFFICES ASSUME NEW a \in CaughtS(UU) PROVE a \in caA
    OBVIOUS
  <2>acc. a \in Acceptors  BY DEF CaughtS
  <2>w. PICK m1 \in UU, m2 \in UU :
          Sig(m1) = a /\ Sig(m2) = a
          /\ m1 \notin Tran(m2) /\ m2 \notin Tran(m1)
    BY DEF CaughtS
  <2>caseA. CASE \E q \in pr : a \in Caught(q)
    <3>1. PICK q \in pr : a \in Caught(q)  BY <2>caseA
    <3>2. a \in MemoP(q).caught  BY <3>1, <1>idp
    <3>3. MemoP(q) \in rP  OBVIOUS
    <3>4. a \in UNION {rc.caught : rc \in rP}  BY <3>2, <3>3
    <3> QED BY <3>4, <1>ca
  <2>caseB. CASE \A q \in pr : a \notin Caught(q)
    <3>cover. ASSUME NEW mm \in UU, Sig(mm) = a
              PROVE \E c \in CaughtCandidates(rP) :
                       Sig(c) = a /\ mm \in MemoP(c).prevtran
      <4>p. PICK q \in pr : mm \in Tran(q)  BY <3>cover
      <4>pM. q \in Messages  BY <1>prMsg
      <4>nc. a \notin Caught(q)  BY <2>caseB
      <4>ihp. MemoPGood(q)  BY <1>ihq
      <4>a. CASE Sig(q) = a
        <5>cand. q \in CaughtCandidates(rP)  BY <1>candRef
        <5>x. CASE mm = q
          <6>1. q \in MemoP(q).prevtran  BY <4>ihp DEF MemoPGood
          <6> QED BY <6>1, <5>x, <5>cand, <4>a
        <5>y. CASE mm # q
          <6>1. mm \in TranExclusive(q)  BY <4>p, <5>y DEF TranExclusive
          <6>2. CASE mm \in MemoP(q).prevtran
            <7> QED BY <6>2, <5>cand, <4>a
          <6>3. CASE mm \notin MemoP(q).prevtran
            <7>1. Sig(q) \in Caught(q)
              BY <6>1, <6>3, <4>a, <2>acc, <3>cover, <4>ihp DEF MemoPGood
            <7> QED BY <7>1, <4>a, <4>nc
          <6> QED BY <6>2, <6>3
        <5> QED BY <5>x, <5>y
      <4>b. CASE Sig(q) # a
        <5>1. mm # q  BY <4>b, <3>cover
        <5>2. mm \in TranExclusive(q)  BY <4>p, <5>1 DEF TranExclusive
        <5>3. /\ Sig(mm) \in DOMAIN MemoP(q).deepestknown
              /\ mm \in MemoP(q).deepestknown[Sig(mm)][2].prevtran
          BY <5>2, <4>nc, <2>acc, <3>cover, <4>ihp DEF MemoPGood
        <5>4. a \in DOMAIN MemoP(q).deepestknown  BY <5>3, <3>cover
        <5>5. MemoP(q).deepestknown[Sig(mm)][2] = MemoP(q).deepestknown[a][2]
          BY <3>cover
        <5>6. mm \in MemoP(q).deepestknown[a][2].prevtran  BY <5>3, <5>5
        <5>cand. MemoP(q).deepestknown[a][2].id \in CaughtCandidates(rP)
          BY <5>4, <1>candDK
        <5>can. MemoP(q).deepestknown[a][2]
                  = MemoP(MemoP(q).deepestknown[a][2].id)
          BY <5>4, <1>ihdkP DEF DeepestKnownCorrectP
        <5>sig. Sig(MemoP(q).deepestknown[a][2].id) = a
          BY <5>4, <1>ihdkP DEF DeepestKnownCorrectP
        <5>7. mm \in MemoP(MemoP(q).deepestknown[a][2].id).prevtran
          BY <5>6, <5>can
        <5> QED BY <5>7, <5>cand, <5>sig
      <4> QED BY <4>a, <4>b
    <3>k1. \E c \in CaughtCandidates(rP) :
             Sig(c) = a /\ m1 \in MemoP(c).prevtran
      BY <3>cover, <2>w
    <3>k2. \E c \in CaughtCandidates(rP) :
             Sig(c) = a /\ m2 \in MemoP(c).prevtran
      BY <3>cover, <2>w
    <3>p1. PICK c1 \in CaughtCandidates(rP) :
             Sig(c1) = a /\ m1 \in MemoP(c1).prevtran
      BY <3>k1
    <3>p2. PICK c2 \in CaughtCandidates(rP) :
             Sig(c2) = a /\ m2 \in MemoP(c2).prevtran
      BY <3>k2
    <3>adom. a \in DOMAIN dkA
      <4>1. a \in SigS(UU)  BY <2>w DEF SigS
      <4> QED BY <4>1, <1>dom
    <3> DEFINE z == dkA[a][2].id
    <3>zU. z \in UU
      BY <1>invA, <3>adom DEF DeepestKnownCorrectUP
    <3>zM. z \in Messages  BY <3>zU, <1>teM
    <3>ihz. MemoPGood(z)  BY <3>zU, <1>ihU
    <3>notboth. ~(c1 \in MemoP(z).prevtran /\ c2 \in MemoP(z).prevtran)
      <4>1. CASE c1 \in MemoP(z).prevtran /\ c2 \in MemoP(z).prevtran
        <5>1. MemoP(c1).prevtran \subseteq MemoP(z).prevtran
          BY <4>1, <3>ihz DEF MemoPGood
        <5>2. MemoP(c2).prevtran \subseteq MemoP(z).prevtran
          BY <4>1, <3>ihz DEF MemoPGood
        <5>3. m1 \in MemoP(z).prevtran /\ m2 \in MemoP(z).prevtran
          BY <3>p1, <3>p2, <5>1, <5>2
        <5>4. m1 \in Tran(m2) \/ m2 \in Tran(m1)
          BY <5>3, <3>ihz DEF MemoPGood
        <5> QED BY <5>4, <2>w
      <4> QED BY <4>1
    <3>fail. ASSUME NEW c, c \in CaughtCandidates(rP), Sig(c) = a,
                    c \notin MemoP(z).prevtran
             PROVE a \in caA
      <4>1. DeepestKnownAssemble(rP)[a][2].prevtran = MemoP(z).prevtran
        BY <3>adom, <1>pt
      <4>2. DeepestKnownAssemble(rP)[Sig(c)][2].prevtran
              = DeepestKnownAssemble(rP)[a][2].prevtran
        BY <3>fail
      <4>3. c \notin DeepestKnownAssemble(rP)[Sig(c)][2].prevtran
        BY <4>1, <4>2, <3>fail
      <4>4. Sig(c) \in Acceptors  BY <3>fail, <2>acc
      <4>5. c \in Test  BY <3>fail, <4>3, <4>4 DEF Test
      <4>6. a \in SigS(Test)  BY <4>5, <3>fail DEF SigS
      <4> QED BY <4>6, <1>ca
    <3>f1. CASE c1 \notin MemoP(z).prevtran
      <4> QED BY <3>f1, <3>p1, <3>fail
    <3>f2. CASE c2 \notin MemoP(z).prevtran
      <4> QED BY <3>f2, <3>p2, <3>fail
    <3> QED BY <3>notboth, <3>f1, <3>f2
  <2> QED BY <2>caseA, <2>caseB
<1> QED BY <1>sound, <1>compl
=============================================================================
