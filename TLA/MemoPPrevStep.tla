----------------------------- MODULE MemoPPrevStep -----------------------------
\* MemoP tower, leg S6: the five prevtran chain properties of MemoP(x) --
\* structure (self / inside Tran / same signer), absorption, total
\* comparability, completeness, and coverage of uncaught signers.
\*
\* Unlike S1/S2/S4 this leg is stated directly about MemoP(x)'s fields
\* rather than about the assemblies: absorption and coverage quantify over
\* the STORED chain, so the unfold (MemoPRec) is needed inside the proof
\* anyway.  The step then reads exactly like the tail of MemoPGood(x).
\*
\* The proof follows the chain one link: by S4 the assembled entry for
\* Sig(x) is MemoP(z1) for a same-signer z1 in x's exclusive history, so
\* MemoP(x).prevtran = {x} \cup MemoP(z1).prevtran and every property
\* reduces to the induction hypothesis at z1, exactly as
\* PrevTranStruct / PrevTranAbsorb / PrevTranChain / PrevTranComplete /
\* PrevTranCovers reduce to their own recursive call.  MemoPDKMaximal
\* replaces DeepestKnownMaximal in the "strictly above the entry" cases.
EXTENDS MemoPDefs, MemoPRec, MemoPDKStep, MemoPDKMaximal, CRefsSubPriors,
        CMessagesSubMC, CFields, CMessageTranClosed, CTranResolve,
        TranSubMessages, CaughtMonotoneTran
LOCAL INSTANCE TLAPS

LEMMA MemoPPrevStep ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         MessageInterface = CMI,
         NEW x \in CMessages,
         \A y \in CTranExcl(x) : MemoPGood(y)
  PROVE /\ x \in MemoP(x).prevtran
        /\ MemoP(x).prevtran \subseteq Tran(x)
        /\ \A y \in MemoP(x).prevtran : Sig(y) = Sig(x)
        /\ \A y \in MemoP(x).prevtran :
             MemoP(y).prevtran \subseteq MemoP(x).prevtran
        /\ \A y1 \in MemoP(x).prevtran : \A y2 \in MemoP(x).prevtran :
             y1 \in Tran(y2) \/ y2 \in Tran(y1)
        /\ (Sig(x) \in Acceptors =>
              \A y \in TranExclusive(x) :
                (Sig(y) = Sig(x) /\ y \notin MemoP(x).prevtran)
                  => Sig(x) \in Caught(x))
        /\ \A y \in TranExclusive(x) :
             (Sig(y) \in Acceptors /\ Sig(y) \notin Caught(x)) =>
               /\ Sig(y) \in DOMAIN MemoP(x).deepestknown
               /\ y \in MemoP(x).deepestknown[Sig(y)][2].prevtran
<1> DEFINE pr == x.priors
<1> DEFINE rP == {MemoP(q) : q \in pr}
<1> DEFINE dka == DeepestKnownAssemble(rP)
\* ------------------------------------------------------------------ prelude
<1>xm. x \in Messages  BY CFields
<1>sand. Refs(x) \subseteq pr /\ pr \subseteq TranExclusive(x)
  BY CRefsSubPriors
<1>teq. TranExclusive(x) = CTranExcl(x)
  <2>1. Tran(x) = CTran(x)  BY CTranResolve
  <2> QED BY <2>1 DEF TranExclusive, CTranExcl
<1>ihTE. \A y \in TranExclusive(x) : MemoPGood(y)  BY <1>teq
<1>teM. TranExclusive(x) \subseteq Messages
  BY <1>xm, TranSubMessages DEF TranExclusive
<1>selfT. x \in Tran(x)  BY DEF Tran
<1>unf. MemoP(x) = MemoR(x, rP)
  <2>1. x \in CMC  BY CMessagesSubMC
  <2>2. CPriors(x) = pr  BY DEF CPriors
  <2> QED BY <2>1, <2>2, MemoPRec
<1>pt. MemoP(x).prevtran = PrevTranAssemble(x, rP)
  BY <1>unf DEF MemoR
<1>dkf. MemoP(x).deepestknown = dka  BY <1>unf DEF MemoR
<1>dkP. DeepestKnownCorrectP(x, dka)  BY MemoPDKStep
<1>dkdom. DOMAIN dka = SigS(TranExclusive(x))
  BY <1>dkP DEF DeepestKnownCorrectP
\* ------------------------------------------------------- coverage of signers
<1>cov. \A y \in TranExclusive(x) :
          (Sig(y) \in Acceptors /\ Sig(y) \notin Caught(x)) =>
            /\ Sig(y) \in DOMAIN MemoP(x).deepestknown
            /\ y \in MemoP(x).deepestknown[Sig(y)][2].prevtran
  <2> SUFFICES ASSUME NEW y \in TranExclusive(x),
                      Sig(y) \in Acceptors, Sig(y) \notin Caught(x)
      PROVE /\ Sig(y) \in DOMAIN MemoP(x).deepestknown
            /\ y \in MemoP(x).deepestknown[Sig(y)][2].prevtran
    OBVIOUS
  <2>sdom. Sig(y) \in DOMAIN dka
    <3>1. Sig(y) \in SigS(TranExclusive(x))  BY DEF SigS
    <3> QED BY <3>1, <1>dkdom
  <2> DEFINE zc == dka[Sig(y)][2].id
  <2>ze. /\ dka[Sig(y)][2] = MemoP(zc)
         /\ zc \in TranExclusive(x)
         /\ Sig(zc) = Sig(y)
    BY <1>dkP, <2>sdom DEF DeepestKnownCorrectP
  <2>zM. zc \in Messages  BY <2>ze, <1>teM
  <2>ihz. MemoPGood(zc)  BY <2>ze, <1>ihTE
  <2>zprev. dka[Sig(y)][2].prevtran = MemoP(zc).prevtran  BY <2>ze
  <2>goal. SUFFICES y \in MemoP(zc).prevtran
    BY <2>sdom, <2>zprev, <1>dkf
  <2>a. CASE y = zc
    <3>1. zc \in MemoP(zc).prevtran  BY <2>ihz DEF MemoPGood
    <3> QED BY <2>a, <3>1
  <2>b. CASE y # zc /\ y \in Tran(zc)
    <3>1. y \in TranExclusive(zc)  BY <2>b DEF TranExclusive
    <3>2. CASE y \in MemoP(zc).prevtran
      <4> QED BY <3>2
    <3>3. CASE y \notin MemoP(zc).prevtran
      <4>1. Sig(zc) \in Caught(zc)
        BY <3>1, <3>3, <2>ze, <2>ihz DEF MemoPGood
      <4>2. zc \in Tran(x)  BY <2>ze DEF TranExclusive
      <4>3. Caught(zc) \subseteq Caught(x)
        BY <4>2, <1>xm, CaughtMonotoneTran
      <4>4. Sig(y) \in Caught(x)  BY <4>1, <4>3, <2>ze
      <4> QED BY <4>4
    <3> QED BY <3>2, <3>3
  <2>c. CASE y # zc /\ zc \in Tran(y)
    <3>1. zc \in TranExclusive(y)  BY <2>c DEF TranExclusive
    <3> QED BY <3>1, <2>sdom, <1>dkP, <1>xm, MemoPDKMaximal
  <2>d. CASE y \notin Tran(zc) /\ zc \notin Tran(y)
    <3>1. y \in Tran(x) /\ zc \in Tran(x)  BY <2>ze DEF TranExclusive
    <3>2. Sig(y) \in CaughtS(Tran(x))  BY <2>d, <3>1, <2>ze DEF CaughtS
    <3>3. Sig(y) \in Caught(x)  BY <3>2 DEF Caught
    <3> QED BY <3>3
  <2> QED BY <2>a, <2>b, <2>c, <2>d
\* -------------------------------------------------------- chain, by one link
<1>rest. /\ x \in MemoP(x).prevtran
         /\ MemoP(x).prevtran \subseteq Tran(x)
         /\ \A y \in MemoP(x).prevtran : Sig(y) = Sig(x)
         /\ \A y \in MemoP(x).prevtran :
              MemoP(y).prevtran \subseteq MemoP(x).prevtran
         /\ \A y1 \in MemoP(x).prevtran : \A y2 \in MemoP(x).prevtran :
              y1 \in Tran(y2) \/ y2 \in Tran(y1)
         /\ (Sig(x) \in Acceptors =>
               \A y \in TranExclusive(x) :
                 (Sig(y) = Sig(x) /\ y \notin MemoP(x).prevtran)
                   => Sig(x) \in Caught(x))
  <2>a. CASE Sig(x) \notin DOMAIN dka
    <3>pt1. MemoP(x).prevtran = {x}
      BY <1>pt, <2>a DEF PrevTranAssemble
    <3>1. x \in MemoP(x).prevtran  BY <3>pt1
    <3>2. MemoP(x).prevtran \subseteq Tran(x)  BY <3>pt1, <1>selfT
    <3>3. \A y \in MemoP(x).prevtran : Sig(y) = Sig(x)  BY <3>pt1
    <3>4. \A y \in MemoP(x).prevtran :
            MemoP(y).prevtran \subseteq MemoP(x).prevtran
      BY <3>pt1
    <3>5. \A y1 \in MemoP(x).prevtran : \A y2 \in MemoP(x).prevtran :
            y1 \in Tran(y2) \/ y2 \in Tran(y1)
      BY <3>pt1, <1>selfT
    <3>6. Sig(x) \in Acceptors =>
            \A y \in TranExclusive(x) :
              (Sig(y) = Sig(x) /\ y \notin MemoP(x).prevtran)
                => Sig(x) \in Caught(x)
      <4> SUFFICES ASSUME Sig(x) \in Acceptors,
                          NEW y \in TranExclusive(x),
                          Sig(y) = Sig(x),
                          y \notin MemoP(x).prevtran
          PROVE Sig(x) \in Caught(x)
        OBVIOUS
      <4>1. Sig(x) \in SigS(TranExclusive(x))  BY DEF SigS
      <4> QED BY <4>1, <1>dkdom, <2>a
    <3> QED BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6
  <2>b. CASE Sig(x) \in DOMAIN dka
    <3> DEFINE z1 == dka[Sig(x)][2].id
    <3>z1. /\ dka[Sig(x)][2] = MemoP(z1)
           /\ z1 \in TranExclusive(x)
           /\ Sig(z1) = Sig(x)
      BY <1>dkP, <2>b DEF DeepestKnownCorrectP
    <3>z1M. z1 \in Messages  BY <3>z1, <1>teM
    <3>ihz. MemoPGood(z1)  BY <3>z1, <1>ihTE
    <3>ptx. MemoP(x).prevtran = {x} \cup MemoP(z1).prevtran
      <4>1. PrevTranAssemble(x, rP)
              = {x} \cup dka[Sig(x)][2].prevtran
        BY <2>b DEF PrevTranAssemble
      <4> QED BY <1>pt, <4>1, <3>z1
    <3>zstruct. /\ z1 \in MemoP(z1).prevtran
                /\ MemoP(z1).prevtran \subseteq Tran(z1)
                /\ \A y \in MemoP(z1).prevtran : Sig(y) = Sig(z1)
      BY <3>ihz DEF MemoPGood
    <3>t1. Tran(z1) \subseteq Tran(x)
      <4>1. z1 \in Tran(x)  BY <3>z1 DEF TranExclusive
      <4> QED BY <4>1, <1>xm DEF TranTrans
    <3>inx. MemoP(z1).prevtran \subseteq Tran(x)
      BY <3>zstruct, <3>t1
    <3>1. x \in MemoP(x).prevtran  BY <3>ptx
    <3>2. MemoP(x).prevtran \subseteq Tran(x)
      BY <3>ptx, <3>inx, <1>selfT
    <3>3. \A y \in MemoP(x).prevtran : Sig(y) = Sig(x)
      BY <3>ptx, <3>zstruct, <3>z1
    <3>4. \A y \in MemoP(x).prevtran :
            MemoP(y).prevtran \subseteq MemoP(x).prevtran
      <4> SUFFICES ASSUME NEW y \in MemoP(x).prevtran
          PROVE MemoP(y).prevtran \subseteq MemoP(x).prevtran
        OBVIOUS
      <4>a. CASE y = x
        <5> QED BY <4>a
      <4>b. CASE y \in MemoP(z1).prevtran
        <5>1. MemoP(y).prevtran \subseteq MemoP(z1).prevtran
          BY <4>b, <3>ihz DEF MemoPGood
        <5> QED BY <5>1, <3>ptx
      <4> QED BY <3>ptx, <4>a, <4>b
    <3>5. \A y1 \in MemoP(x).prevtran : \A y2 \in MemoP(x).prevtran :
            y1 \in Tran(y2) \/ y2 \in Tran(y1)
      <4> SUFFICES ASSUME NEW y1 \in MemoP(x).prevtran,
                          NEW y2 \in MemoP(x).prevtran
          PROVE y1 \in Tran(y2) \/ y2 \in Tran(y1)
        OBVIOUS
      <4>aa. CASE y1 = x /\ y2 = x
        <5> QED BY <4>aa, <1>selfT
      <4>ab. CASE y1 = x /\ y2 \in MemoP(z1).prevtran
        <5>1. y2 \in Tran(x)  BY <4>ab, <3>inx
        <5> QED BY <5>1, <4>ab
      <4>ba. CASE y1 \in MemoP(z1).prevtran /\ y2 = x
        <5>1. y1 \in Tran(x)  BY <4>ba, <3>inx
        <5> QED BY <5>1, <4>ba
      <4>bb. CASE y1 \in MemoP(z1).prevtran /\ y2 \in MemoP(z1).prevtran
        <5> QED BY <4>bb, <3>ihz DEF MemoPGood
      <4> QED BY <3>ptx, <4>aa, <4>ab, <4>ba, <4>bb
    <3>6. Sig(x) \in Acceptors =>
            \A y \in TranExclusive(x) :
              (Sig(y) = Sig(x) /\ y \notin MemoP(x).prevtran)
                => Sig(x) \in Caught(x)
      <4> SUFFICES ASSUME Sig(x) \in Acceptors,
                          NEW w \in TranExclusive(x),
                          Sig(w) = Sig(x),
                          w \notin MemoP(x).prevtran
          PROVE Sig(x) \in Caught(x)
        OBVIOUS
      <4>wnot1. w \notin MemoP(z1).prevtran  BY <3>ptx
      <4>wneq. w # z1  BY <4>wnot1, <3>zstruct
      <4>c1. CASE w \in Tran(z1)
        <5>1. w \in TranExclusive(z1)  BY <4>c1, <4>wneq DEF TranExclusive
        <5>2. Sig(z1) \in Caught(z1)
          BY <5>1, <4>wnot1, <3>z1, <3>ihz DEF MemoPGood
        <5>3. z1 \in Tran(x)  BY <3>z1 DEF TranExclusive
        <5>4. Caught(z1) \subseteq Caught(x)
          BY <5>3, <1>xm, CaughtMonotoneTran
        <5> QED BY <5>2, <5>4, <3>z1
      <4>c2. CASE z1 \in Tran(w)
        <5>1. z1 \in TranExclusive(w)  BY <4>c2, <4>wneq DEF TranExclusive
        <5> QED BY <5>1, <2>b, <1>dkP, <1>xm, MemoPDKMaximal
      <4>c3. CASE w \notin Tran(z1) /\ z1 \notin Tran(w)
        <5>1. w \in Tran(x) /\ z1 \in Tran(x)  BY <3>z1 DEF TranExclusive
        <5>2. Sig(x) \in CaughtS(Tran(x))
          BY <4>c3, <5>1, <3>z1 DEF CaughtS
        <5> QED BY <5>2 DEF Caught
      <4> QED BY <4>c1, <4>c2, <4>c3
    <3> QED BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6
  <2> QED BY <2>a, <2>b
<1> QED BY <1>rest, <1>cov
=============================================================================
