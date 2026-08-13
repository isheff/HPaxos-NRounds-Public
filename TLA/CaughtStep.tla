---------------------------- MODULE CaughtStep ----------------------------
\*   MemoRec, DeepestKnownInv, DeepestKnownMaximal, PrevTranStruct,
\*   PrevTranAbsorb, PrevTranChain, PrevTranComplete, PrevTranCovers,
\*   TranExclusiveRefs, TranSubMessages, CaughtMonotoneTran -> cited lemmas
\*   TLAPS -> proof-only
EXTENDS RecursiveWellFormed, MemoRec, DeepestKnownInv, DeepestKnownStep,
        DeepestKnownMaximalG,
        PrevTranStruct, PrevTranAbsorb, PrevTranChain, PrevTranComplete,
        PrevTranCovers, TranExclusiveCover, TranSubMessages, CaughtMonotoneTran
LOCAL INSTANCE TLAPS

\* The generalized step for CaughtRec: given correct caught memos for ANY
\* set S between Refs(x) and TranExclusive(x), the caught assembly over S's
\* memos equals Caught(x).
\* Soundness: inherited caughts are caught by monotonicity; a candidate off
\* its signer's assembled chain witnesses a fork (via PrevTranComplete /
\* DeepestKnownMaximalG). Completeness: two incomparable same-signer
\* witnesses each sit on the chain of SOME candidate (PrevTranCovers); if
\* both candidates passed the test, absorption would put both witnesses on
\* one totally-ordered chain (PrevTranChain) -- contradiction, so some
\* candidate fails the test and the signer is collected.
LEMMA CaughtStep ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         NEW x \in Messages,
         NEW S, Refs(x) \subseteq S, S \subseteq TranExclusive(x),
         \A p \in S : MemoCaught(p) = Caught(p)
  PROVE CaughtAssemble({Memo(p) : p \in S}) = Caught(x)
<1> DEFINE R == S
<1> DEFINE recs == {Memo(p) : p \in R}
<1> DEFINE caA == CaughtAssemble(recs)
<1> DEFINE dkA == DeepestKnownAssemble(recs)
<1> DEFINE Test == {y \in CaughtCandidates(recs) :
                      /\ Sig(y) \in Acceptors
                      /\ y \notin DeepestKnownAssemble(recs)[Sig(y)][2].prevtran}
<1> HIDE DEF Test
<1>ih. \A p \in R : MemoCaught(p) = Caught(p)  OBVIOUS
<1>rsub. R \subseteq TranExclusive(x)  OBVIOUS
<1>rM. R \subseteq Messages  BY <1>rsub, TranSubMessages DEF TranExclusive
<1>tex. TranExclusive(x) = UNION {Tran(p) : p \in R}  BY TranExclusiveCover
<1>texPP. \A p \in R : TranExclusive(p) \subseteq TranExclusive(x)
  BY <1>tex DEF TranExclusive
<1>pTE. \A p \in R : p \in TranExclusive(x)  BY <1>rsub
<1>teM. TranExclusive(x) \subseteq Messages
  BY TranSubMessages DEF TranExclusive
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
<1>invA. DeepestKnownCorrect(x, dkA)
  <2>1. \A p \in R : DeepestKnownInvariant(p)  BY <1>rM, DeepestKnownInv
  <2> QED BY <2>1, DeepestKnownStep
<1>dom. DOMAIN dkA = SigS(TranExclusive(x))
  BY <1>invA DEF DeepestKnownCorrect
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
    BY <1>invA DEF DeepestKnownCorrect
  <2> QED BY <2>can DEF PrevTran
<1>candTE. \A y \in CaughtCandidates(recs) : y \in TranExclusive(x)
  <2> SUFFICES ASSUME NEW y \in CaughtCandidates(recs)
      PROVE y \in TranExclusive(x)
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
<1>sound. caA \subseteq Caught(x)
  <2>refs. UNION {rc.caught : rc \in recs} \subseteq Caught(x)
    <3> SUFFICES ASSUME NEW a \in UNION {rc.caught : rc \in recs}
        PROVE a \in Caught(x)
      OBVIOUS
    <3>1. PICK rc \in recs : a \in rc.caught  OBVIOUS
    <3>2. PICK p \in R : rc = Memo(p)  OBVIOUS
    <3>3. a \in Caught(p)  BY <3>1, <3>2, <1>idp, <1>ih
    <3>4. p \in Tran(x)  BY <1>pTE DEF TranExclusive
    <3>5. Caught(p) \subseteq Caught(x)  BY <3>4, CaughtMonotoneTran
    <3> QED BY <3>3, <3>5
  <2>test. SigS(Test) \subseteq Caught(x)
    <3> SUFFICES ASSUME NEW a \in SigS(Test) PROVE a \in Caught(x)  OBVIOUS
    <3>y. PICK y \in Test : a = Sig(y)  BY DEF SigS
    <3>yc. y \in CaughtCandidates(recs) /\ Sig(y) \in Acceptors
             /\ y \notin DeepestKnownAssemble(recs)[Sig(y)][2].prevtran
      BY <3>y DEF Test
    <3>yTE. y \in TranExclusive(x)  BY <3>yc, <1>candTE
    <3>sdom. Sig(y) \in DOMAIN dkA
      <4>1. Sig(y) \in SigS(TranExclusive(x))  BY <3>yTE DEF SigS
      <4> QED BY <4>1, <1>dom
    <3> DEFINE zs == dkA[Sig(y)][2].id
    <3>ynot. y \notin PrevTran(zs)  BY <3>yc, <3>sdom, <1>pt
    <3>ze. zs \in TranExclusive(x) /\ Sig(zs) = Sig(y)
      BY <1>invA, <3>sdom DEF DeepestKnownCorrect
    <3>zM. zs \in Messages  BY <3>ze, <1>teM
    <3>yM. y \in Messages  BY <3>yTE, <1>teM
    <3>yneq. y # zs
      <4>1. zs \in PrevTran(zs)  BY <3>zM, PrevTranStruct
      <4> QED BY <4>1, <3>ynot
    <3>c1. CASE y \in Tran(zs)
      <4>1. y \in TranExclusive(zs)  BY <3>c1, <3>yneq DEF TranExclusive
      <4>2. Sig(zs) \in Caught(zs)
        BY <4>1, <3>ynot, <3>ze, <3>zM, <3>yc, PrevTranComplete
      <4>3. zs \in Tran(x)  BY <3>ze DEF TranExclusive
      <4>4. Caught(zs) \subseteq Caught(x)  BY <4>3, CaughtMonotoneTran
      <4> QED BY <4>2, <4>4, <3>ze, <3>y
    <3>c2. CASE zs \in Tran(y)
      <4>1. zs \in TranExclusive(y)  BY <3>c2, <3>yneq DEF TranExclusive
      <4> QED BY <4>1, <3>sdom, <3>yTE, <1>invA, DeepestKnownMaximalG
    <3>c3. CASE y \notin Tran(zs) /\ zs \notin Tran(y)
      <4>1. y \in Tran(x) /\ zs \in Tran(x)
        BY <3>yTE, <3>ze DEF TranExclusive
      <4>2. Sig(y) \in CaughtS(Tran(x))
        BY <3>c3, <4>1, <3>ze, <3>yc DEF CaughtS
      <4> QED BY <4>2, <3>y DEF Caught
    <3> QED BY <3>c1, <3>c2, <3>c3
  <2> QED BY <1>ca, <2>refs, <2>test
\* ------------------------------------------------------------ completeness
<1>compl. Caught(x) \subseteq caA
  <2> SUFFICES ASSUME NEW a \in Caught(x) PROVE a \in caA
    OBVIOUS
  <2>acc. a \in Acceptors  BY DEF Caught, CaughtS
  <2>w. PICK m1 \in Tran(x), m2 \in Tran(x) :
          Sig(m1) = a /\ Sig(m2) = a /\ m1 \notin Tran(m2) /\ m2 \notin Tran(m1)
    BY DEF Caught, CaughtS
  <2>ne. m1 # x /\ m2 # x  BY <2>w
  <2>te. m1 \in TranExclusive(x) /\ m2 \in TranExclusive(x)
    BY <2>ne, <2>w DEF TranExclusive
  <2>caseA. CASE \E p \in R : a \in Caught(p)
    <3>1. PICK p \in R : a \in Caught(p)  BY <2>caseA
    <3>2. a \in Memo(p).caught  BY <3>1, <1>idp, <1>ih
    <3>3. Memo(p) \in recs  OBVIOUS
    <3>4. a \in UNION {rc.caught : rc \in recs}  BY <3>2, <3>3
    <3> QED BY <3>4, <1>ca
  <2>caseB. CASE \A p \in R : a \notin Caught(p)
    <3>cover. ASSUME NEW mm \in TranExclusive(x), Sig(mm) = a
              PROVE \E c \in CaughtCandidates(recs) :
                       Sig(c) = a /\ mm \in PrevTran(c)
      <4>p. PICK p \in R : mm \in Tran(p)  BY <1>tex, <3>cover
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
      BY <3>cover, <2>te, <2>w
    <3>k2. \E c \in CaughtCandidates(recs) : Sig(c) = a /\ m2 \in PrevTran(c)
      BY <3>cover, <2>te, <2>w
    <3>p1. PICK c1 \in CaughtCandidates(recs) :
             Sig(c1) = a /\ m1 \in PrevTran(c1)
      BY <3>k1
    <3>p2. PICK c2 \in CaughtCandidates(recs) :
             Sig(c2) = a /\ m2 \in PrevTran(c2)
      BY <3>k2
    <3>adom. a \in DOMAIN dkA
      <4>1. a \in SigS(TranExclusive(x))  BY <2>te, <2>w DEF SigS
      <4> QED BY <4>1, <1>dom
    <3> DEFINE z == dkA[a][2].id
    <3>zM. z \in Messages
      <4>1. z \in TranExclusive(x)
        BY <1>invA, <3>adom DEF DeepestKnownCorrect
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
====================================================================
