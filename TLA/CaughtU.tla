-------------------------------- MODULE CaughtU --------------------------------
\* Plan step (b) toward CWellFormedRec: the (pr, U)-virtualized CaughtStep.
\* For a FINITE prior set pr \subseteq Messages -- with no assembling message
\* -- the caught assembly over pr's memos equals CaughtS(U) for U := UNION
\* {Tran(p) : p \in pr}.  Soundness: inherited caughts have their witnesses
\* inside a member's closure (\subseteq U); a candidate off its signer's
\* assembled chain witnesses a fork (PrevTranComplete / DeepestKnownMaximalU).
\* Completeness: two incomparable same-signer witnesses in U each sit on the
\* chain of SOME candidate (PrevTranCovers); if both candidates passed the
\* test, absorption would put both witnesses on one totally-ordered chain
\* (PrevTranChain) -- so some candidate fails and the signer is collected.
EXTENDS MemoUDefs, MemoRec, DeepestKnownInv, DeepestKnownU,
        DeepestKnownMaximalU, CaughtRec, PrevTranStruct, PrevTranAbsorb,
        PrevTranChain, PrevTranComplete, PrevTranCovers, TranSubMessages
LOCAL INSTANCE TLAPS

LEMMA CaughtU ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         NEW pr, pr \subseteq Messages, IsFiniteSet(pr)
  PROVE CaughtAssemble({Memo(p) : p \in pr})
          = CaughtS(UNION {Tran(p) : p \in pr})
<1> DEFINE R == pr
<1> DEFINE recs == {Memo(p) : p \in R}
<1> DEFINE caA == CaughtAssemble(recs)
<1> DEFINE dkA == DeepestKnownAssemble(recs)
<1> DEFINE UU == UNION {Tran(p) : p \in R}
<1> DEFINE Test == {y \in CaughtCandidates(recs) :
                      /\ Sig(y) \in Acceptors
                      /\ y \notin DeepestKnownAssemble(recs)[Sig(y)][2].prevtran}
<1> HIDE DEF Test
<1>ih. \A p \in R : MemoCaught(p) = Caught(p)  BY CaughtRec
<1>rM. R \subseteq Messages  OBVIOUS
<1>texP. \A p \in R : Tran(p) \subseteq UU  OBVIOUS
<1>texPP. \A p \in R : TranExclusive(p) \subseteq UU
  BY <1>texP DEF TranExclusive
<1>pTE. \A p \in R : p \in UU
  <2> SUFFICES ASSUME NEW p \in R PROVE p \in UU  OBVIOUS
  <2>1. p \in Tran(p)  BY DEF Tran
  <2> QED BY <2>1
<1>teM. UU \subseteq Messages
  <2> SUFFICES ASSUME NEW z \in UU PROVE z \in Messages  OBVIOUS
  <2>1. PICK p \in R : z \in Tran(p)  OBVIOUS
  <2> QED BY <2>1, TranSubMessages
<1>ucl. \A z \in UU : Tran(z) \subseteq UU
  <2> SUFFICES ASSUME NEW z \in UU PROVE Tran(z) \subseteq UU  OBVIOUS
  <2>1. PICK p \in R : z \in Tran(p)  OBVIOUS
  <2>2. Tran(z) \subseteq Tran(p)  BY <2>1 DEF TranTrans
  <2> QED BY <2>2, <1>texP
<1>idp. \A p \in R : /\ Memo(p).id = p
                     /\ Memo(p).deepestknown = DeepestKnown(p)
                     /\ Memo(p).caught = MemoCaught(p)
  <2> SUFFICES ASSUME NEW p \in R
      PROVE /\ Memo(p).id = p
            /\ Memo(p).deepestknown = DeepestKnown(p)
            /\ Memo(p).caught = MemoCaught(p)
    OBVIOUS
  <2>1. p \in Messages  BY <1>rM
  <2>2. Memo(p) = MemoR(p, {Memo(q) : q \in Refs(p)})
    BY <2>1, MemoRec
  <2> QED BY <2>2 DEF MemoR, DeepestKnown, MemoCaught
<1>invA. DeepestKnownCorrectU(UU, dkA)
  BY DeepestKnownU
<1>dom. DOMAIN dkA = SigS(UU)
  BY <1>invA DEF DeepestKnownCorrectU
<1>ca. caA = (UNION {rc.caught : rc \in recs}) \cup SigS(Test)
  BY DEF CaughtAssemble, Test
<1>pt. \A s \in DOMAIN dkA :
         DeepestKnownAssemble(recs)[s][2].prevtran
           = PrevTran(dkA[s][2].id)
  <2> SUFFICES ASSUME NEW s \in DOMAIN dkA
      PROVE DeepestKnownAssemble(recs)[s][2].prevtran
              = PrevTran(dkA[s][2].id)
    OBVIOUS
  <2>can. dkA[s][2] = Memo(dkA[s][2].id)
    BY <1>invA DEF DeepestKnownCorrectU
  <2> QED BY <2>can DEF PrevTran
<1>candTE. \A y \in CaughtCandidates(recs) : y \in UU
  <2> SUFFICES ASSUME NEW y \in CaughtCandidates(recs)
      PROVE y \in UU
    OBVIOUS
  <2>split. \/ y \in {rc.id : rc \in recs}
            \/ y \in UNION {MemoDKMessages(rc) : rc \in recs}
    BY DEF CaughtCandidates
  <2>a. CASE y \in {rc.id : rc \in recs}
    <3>1. PICK rc \in recs : y = rc.id  BY <2>a
    <3>2. PICK p \in R : rc = Memo(p)  OBVIOUS
    <3>3. y = p  BY <3>1, <3>2, <1>idp
    <3> QED BY <3>3, <1>pTE
  <2>b. CASE y \in UNION {MemoDKMessages(rc) : rc \in recs}
    <3>1. PICK rc \in recs : y \in MemoDKMessages(rc)  BY <2>b
    <3>2. PICK p \in R : rc = Memo(p)  OBVIOUS
    <3>3. PICK s \in DOMAIN DeepestKnown(p) : y = DeepestKnown(p)[s][2].id
      BY <3>1, <3>2, <1>idp DEF MemoDKMessages
    <3>invp. DeepestKnownInvariant(p)  BY <1>rM, DeepestKnownInv
    <3>4. y \in TranExclusive(p)  BY <3>3, <3>invp DEF DeepestKnownInvariant
    <3> QED BY <3>4, <1>texPP
  <2> QED BY <2>split, <2>a, <2>b
<1>candRef. \A p \in R : p \in CaughtCandidates(recs)
  <2> SUFFICES ASSUME NEW p \in R PROVE p \in CaughtCandidates(recs)  OBVIOUS
  <2>1. Memo(p) \in recs  OBVIOUS
  <2>2. Memo(p).id = p  BY <1>idp
  <2> QED BY <2>1, <2>2 DEF CaughtCandidates
<1>candDK. \A p \in R : \A s \in DOMAIN DeepestKnown(p) :
             DeepestKnown(p)[s][2].id \in CaughtCandidates(recs)
  <2> SUFFICES ASSUME NEW p \in R, NEW s \in DOMAIN DeepestKnown(p)
      PROVE DeepestKnown(p)[s][2].id \in CaughtCandidates(recs)
    OBVIOUS
  <2>1. Memo(p) \in recs  OBVIOUS
  <2>2. Memo(p).deepestknown = DeepestKnown(p)  BY <1>idp
  <2>3. DeepestKnown(p)[s][2].id \in MemoDKMessages(Memo(p))
    BY <2>2 DEF MemoDKMessages
  <2> QED BY <2>1, <2>3 DEF CaughtCandidates
\* -------------------------------------------------------------- soundness
<1>sound. caA \subseteq CaughtS(UU)
  <2>refs. UNION {rc.caught : rc \in recs} \subseteq CaughtS(UU)
    <3> SUFFICES ASSUME NEW a \in UNION {rc.caught : rc \in recs}
        PROVE a \in CaughtS(UU)
      OBVIOUS
    <3>1. PICK rc \in recs : a \in rc.caught  OBVIOUS
    <3>2. PICK p \in R : rc = Memo(p)  OBVIOUS
    <3>3. a \in Caught(p)  BY <3>1, <3>2, <1>idp, <1>ih
    <3>4. PICK m1 \in Tran(p), m2 \in Tran(p) :
            /\ Sig(m1) = a /\ Sig(m2) = a
            /\ m1 \notin Tran(m2) /\ m2 \notin Tran(m1)
      BY <3>3 DEF Caught, CaughtS
    <3>5. a \in Acceptors  BY <3>3 DEF Caught, CaughtS
    <3>6. m1 \in UU /\ m2 \in UU  BY <3>4, <1>texP
    <3> QED BY <3>4, <3>5, <3>6 DEF CaughtS
  <2>test. SigS(Test) \subseteq CaughtS(UU)
    <3> SUFFICES ASSUME NEW a \in SigS(Test) PROVE a \in CaughtS(UU)  OBVIOUS
    <3>y. PICK y \in Test : a = Sig(y)  BY DEF SigS
    <3>yc. y \in CaughtCandidates(recs) /\ Sig(y) \in Acceptors
             /\ y \notin DeepestKnownAssemble(recs)[Sig(y)][2].prevtran
      BY <3>y DEF Test
    <3>yTE. y \in UU  BY <3>yc, <1>candTE
    <3>sdom. Sig(y) \in DOMAIN dkA
      <4>1. Sig(y) \in SigS(UU)  BY <3>yTE DEF SigS
      <4> QED BY <4>1, <1>dom
    <3> DEFINE zs == dkA[Sig(y)][2].id
    <3>ynot. y \notin PrevTran(zs)  BY <3>yc, <3>sdom, <1>pt
    <3>ze. zs \in UU /\ Sig(zs) = Sig(y)
      BY <1>invA, <3>sdom DEF DeepestKnownCorrectU
    <3>zM. zs \in Messages  BY <3>ze, <1>teM
    <3>yM. y \in Messages  BY <3>yTE, <1>teM
    <3>yneq. y # zs
      <4>1. zs \in PrevTran(zs)  BY <3>zM, PrevTranStruct
      <4> QED BY <4>1, <3>ynot
    <3>c1. CASE y \in Tran(zs)
      <4>1. y \in TranExclusive(zs)  BY <3>c1, <3>yneq DEF TranExclusive
      <4>2. Sig(zs) \in Caught(zs)
        BY <4>1, <3>ynot, <3>ze, <3>zM, <3>yc, PrevTranComplete
      <4>3. PICK m1 \in Tran(zs), m2 \in Tran(zs) :
              /\ Sig(m1) = Sig(zs) /\ Sig(m2) = Sig(zs)
              /\ m1 \notin Tran(m2) /\ m2 \notin Tran(m1)
        BY <4>2 DEF Caught, CaughtS
      <4>4. m1 \in UU /\ m2 \in UU  BY <4>3, <3>ze, <1>ucl
      <4> QED BY <4>3, <4>4, <3>ze, <3>y, <3>yc DEF CaughtS
    <3>c2. CASE zs \in Tran(y)
      <4>1. zs \in TranExclusive(y)  BY <3>c2, <3>yneq DEF TranExclusive
      <4> QED BY <4>1, <3>sdom, <3>yTE, <1>teM, <1>invA, DeepestKnownMaximalU
    <3>c3. CASE y \notin Tran(zs) /\ zs \notin Tran(y)
      <4>1. y \in UU /\ zs \in UU
        BY <3>yTE, <3>ze
      <4> QED BY <3>c3, <4>1, <3>ze, <3>yc, <3>y DEF CaughtS
    <3> QED BY <3>c1, <3>c2, <3>c3
  <2> QED BY <1>ca, <2>refs, <2>test
\* ------------------------------------------------------------ completeness
<1>compl. CaughtS(UU) \subseteq caA
  <2> SUFFICES ASSUME NEW a \in CaughtS(UU) PROVE a \in caA
    OBVIOUS
  <2>acc. a \in Acceptors  BY DEF CaughtS
  <2>w. PICK m1 \in UU, m2 \in UU :
          Sig(m1) = a /\ Sig(m2) = a /\ m1 \notin Tran(m2) /\ m2 \notin Tran(m1)
    BY DEF CaughtS
  <2>caseA. CASE \E p \in R : a \in Caught(p)
    <3>1. PICK p \in R : a \in Caught(p)  BY <2>caseA
    <3>2. a \in Memo(p).caught  BY <3>1, <1>idp, <1>ih
    <3>3. Memo(p) \in recs  OBVIOUS
    <3>4. a \in UNION {rc.caught : rc \in recs}  BY <3>2, <3>3
    <3> QED BY <3>4, <1>ca
  <2>caseB. CASE \A p \in R : a \notin Caught(p)
    <3>cover. ASSUME NEW mm \in UU, Sig(mm) = a
              PROVE \E c \in CaughtCandidates(recs) :
                       Sig(c) = a /\ mm \in PrevTran(c)
      <4>p. PICK p \in R : mm \in Tran(p)  BY <3>cover
      <4>pM. p \in Messages  BY <1>rM
      <4>nc. a \notin Caught(p)  BY <2>caseB
      <4>a. CASE Sig(p) = a
        <5>cand. p \in CaughtCandidates(recs)  BY <1>candRef
        <5>x. CASE mm = p
          <6>1. p \in PrevTran(p)  BY <4>pM, PrevTranStruct
          <6> QED BY <6>1, <5>x, <5>cand, <4>a
        <5>y. CASE mm # p
          <6>1. mm \in TranExclusive(p)  BY <4>p, <5>y DEF TranExclusive
          <6>2. CASE mm \in PrevTran(p)
            <7> QED BY <6>2, <5>cand, <4>a
          <6>3. CASE mm \notin PrevTran(p)
            <7>1. Sig(p) \in Caught(p)
              BY <6>1, <6>3, <4>a, <4>pM, <2>acc, <3>cover, PrevTranComplete
            <7> QED BY <7>1, <4>a, <4>nc
          <6> QED BY <6>2, <6>3
        <5> QED BY <5>x, <5>y
      <4>b. CASE Sig(p) # a
        <5>1. mm # p  BY <4>b, <3>cover
        <5>2. mm \in TranExclusive(p)  BY <4>p, <5>1 DEF TranExclusive
        <5>3. /\ Sig(mm) \in DOMAIN DeepestKnown(p)
              /\ mm \in PrevTran(DeepestKnown(p)[Sig(mm)][2].id)
          BY <5>2, <4>pM, <4>nc, <2>acc, <3>cover, PrevTranCovers
        <5>4. a \in DOMAIN DeepestKnown(p)  BY <5>3, <3>cover
        <5>5. DeepestKnown(p)[Sig(mm)][2].id = DeepestKnown(p)[a][2].id
          BY <3>cover
        <5>6. mm \in PrevTran(DeepestKnown(p)[a][2].id)  BY <5>3, <5>5
        <5>cand. DeepestKnown(p)[a][2].id \in CaughtCandidates(recs)
          BY <5>4, <1>candDK
        <5>invp. DeepestKnownInvariant(p)  BY <4>pM, DeepestKnownInv
        <5>sig. Sig(DeepestKnown(p)[a][2].id) = a
          BY <5>invp, <5>4 DEF DeepestKnownInvariant
        <5> QED BY <5>6, <5>cand, <5>sig
      <4> QED BY <4>a, <4>b
    <3>k1. \E c \in CaughtCandidates(recs) : Sig(c) = a /\ m1 \in PrevTran(c)
      BY <3>cover, <2>w
    <3>k2. \E c \in CaughtCandidates(recs) : Sig(c) = a /\ m2 \in PrevTran(c)
      BY <3>cover, <2>w
    <3>p1. PICK c1 \in CaughtCandidates(recs) :
             Sig(c1) = a /\ m1 \in PrevTran(c1)
      BY <3>k1
    <3>p2. PICK c2 \in CaughtCandidates(recs) :
             Sig(c2) = a /\ m2 \in PrevTran(c2)
      BY <3>k2
    <3>adom. a \in DOMAIN dkA
      <4>1. a \in SigS(UU)  BY <2>w DEF SigS
      <4> QED BY <4>1, <1>dom
    <3> DEFINE z == dkA[a][2].id
    <3>zM. z \in Messages
      <4>1. z \in UU
        BY <1>invA, <3>adom DEF DeepestKnownCorrectU
      <4> QED BY <4>1, <1>teM
    <3>notboth. ~(c1 \in PrevTran(z) /\ c2 \in PrevTran(z))
      <4>1. CASE c1 \in PrevTran(z) /\ c2 \in PrevTran(z)
        <5>1. PrevTran(c1) \subseteq PrevTran(z)
          BY <4>1, <3>zM, PrevTranAbsorb
        <5>2. PrevTran(c2) \subseteq PrevTran(z)
          BY <4>1, <3>zM, PrevTranAbsorb
        <5>3. m1 \in PrevTran(z) /\ m2 \in PrevTran(z)
          BY <3>p1, <3>p2, <5>1, <5>2
        <5>4. m1 \in Tran(m2) \/ m2 \in Tran(m1)
          BY <5>3, <3>zM, PrevTranChain
        <5> QED BY <5>4, <2>w
      <4> QED BY <4>1
    <3>fail. ASSUME NEW c, c \in CaughtCandidates(recs), Sig(c) = a,
                    c \notin PrevTran(z)
             PROVE a \in caA
      <4>1. DeepestKnownAssemble(recs)[a][2].prevtran = PrevTran(z)
        BY <3>adom, <1>pt
      <4>2. DeepestKnownAssemble(recs)[Sig(c)][2].prevtran
              = DeepestKnownAssemble(recs)[a][2].prevtran
        BY <3>fail
      <4>3. c \notin DeepestKnownAssemble(recs)[Sig(c)][2].prevtran
        BY <4>1, <4>2, <3>fail
      <4>4. Sig(c) \in Acceptors  BY <3>fail, <2>acc
      <4>5. c \in Test  BY <3>fail, <4>3, <4>4 DEF Test
      <4>6. a \in SigS(Test)  BY <4>5, <3>fail DEF SigS
      <4> QED BY <4>6, <1>ca
    <3>f1. CASE c1 \notin PrevTran(z)
      <4> QED BY <3>f1, <3>p1, <3>fail
    <3>f2. CASE c2 \notin PrevTran(z)
      <4> QED BY <3>f2, <3>p2, <3>fail
    <3> QED BY <3>notboth, <3>f1, <3>f2
  <2> QED BY <2>caseA, <2>caseB
<1> QED BY <1>sound, <1>compl
=============================================================================
