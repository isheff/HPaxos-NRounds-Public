------------------------- MODULE PrevTranComplete -------------------------
\*   TranExclusiveInduction, PrevTranRec, DeepestKnownInv, PrevTranStruct,
\*   DeepestKnownMaximal, CaughtMonotoneTran, TranSubMessages -> cited
\*   TLAPS -> proof-only
EXTENDS RecursiveWellFormed, TranExclusiveInduction, PrevTranRec,
        DeepestKnownInv, PrevTranStruct, DeepestKnownMaximal,
        CaughtMonotoneTran, TranSubMessages
LOCAL INSTANCE TLAPS

\* Induction motive, module-level so TranExclusiveInduction can instantiate
\* it by name.
PrevTranCompleteP(z) ==
  \A y \in TranExclusive(z) :
    (Sig(y) = Sig(z) /\ Sig(z) \in Acceptors /\ y \notin PrevTran(z))
      => Sig(z) \in Caught(z)

\* Chain completeness: if an acceptor is NOT caught as of z, then every
\* message it signed in z's exclusive history lies on z's prevtran chain.
\* (Stated contrapositively: a same-signer ancestor off the chain is
\* evidence of a fork.) Induction along the chain: an off-chain ancestor is
\* either incomparable with the chain head z1 (immediate fork), strictly
\* below it (fork inside Tran(z1), by IH), or strictly above it
\* (impossible, by the entry's maximality).
LEMMA PrevTranComplete ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         NEW z \in Messages, NEW y \in TranExclusive(z),
         Sig(y) = Sig(z), Sig(z) \in Acceptors,
         y \notin PrevTran(z)
  PROVE Sig(z) \in Caught(z)
<1>cl. \A x \in Messages :
         (\A yy \in TranExclusive(x) : PrevTranCompleteP(yy))
           => PrevTranCompleteP(x)
  <2> SUFFICES ASSUME NEW x \in Messages,
                      \A yy \in TranExclusive(x) : PrevTranCompleteP(yy),
                      NEW w \in TranExclusive(x),
                      Sig(w) = Sig(x), Sig(x) \in Acceptors,
                      w \notin PrevTran(x)
      PROVE Sig(x) \in Caught(x)
    BY DEF PrevTranCompleteP
  <2>sdom. Sig(x) \in DOMAIN DeepestKnown(x)
    <3>inv. DeepestKnownInvariant(x)  BY DeepestKnownInv
    <3>1. Sig(x) \in SigS(TranExclusive(x))  BY DEF SigS
    <3> QED BY <3>1, <3>inv DEF DeepestKnownInvariant
  <2> DEFINE z1 == DeepestKnown(x)[Sig(x)][2].id
  <2>rec. PrevTran(x) = {x} \cup PrevTran(z1)
    BY PrevTranRec, <2>sdom
  <2>inv. DeepestKnownInvariant(x)  BY DeepestKnownInv
  <2>z1. z1 \in TranExclusive(x) /\ Sig(z1) = Sig(x)
    BY <2>inv, <2>sdom DEF DeepestKnownInvariant
  <2>z1M. z1 \in Messages  BY <2>z1, TranSubMessages DEF TranExclusive
  <2>wM. w \in Messages  BY TranSubMessages DEF TranExclusive
  <2>wnot1. w \notin PrevTran(z1)  BY <2>rec
  <2>wneq. w # z1
    <3>1. z1 \in PrevTran(z1)  BY <2>z1M, PrevTranStruct
    <3> QED BY <3>1, <2>wnot1
  <2>c1. CASE w \in Tran(z1)
    <3>1. w \in TranExclusive(z1)  BY <2>c1, <2>wneq DEF TranExclusive
    <3>2. PrevTranCompleteP(z1)  BY <2>z1
    <3>3. Sig(z1) \in Caught(z1)
      BY <3>1, <3>2, <2>z1, <2>wnot1 DEF PrevTranCompleteP
    <3>4. z1 \in Tran(x)  BY <2>z1 DEF TranExclusive
    <3>5. Caught(z1) \subseteq Caught(x)  BY <3>4, CaughtMonotoneTran
    <3> QED BY <3>3, <3>5, <2>z1
  <2>c2. CASE z1 \in Tran(w)
    <3>1. z1 \in TranExclusive(w)  BY <2>c2, <2>wneq DEF TranExclusive
    <3> QED BY <3>1, <2>sdom, DeepestKnownMaximal
  <2>c3. CASE w \notin Tran(z1) /\ z1 \notin Tran(w)
    <3>1. w \in Tran(x) /\ z1 \in Tran(x)  BY <2>z1 DEF TranExclusive
    <3>2. Sig(x) \in CaughtS(Tran(x))
      BY <2>c3, <3>1, <2>z1 DEF CaughtS
    <3> QED BY <3>2 DEF Caught
  <2> QED BY <2>c1, <2>c2, <2>c3
<1>ind. PrevTranCompleteP(z)  BY <1>cl, TranExclusiveInduction
<1> QED BY <1>ind DEF PrevTranCompleteP
====================================================================
