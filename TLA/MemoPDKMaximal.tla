---------------------------- MODULE MemoPDKMaximal ----------------------------
\* The P-side analogue of DeepestKnownMaximal, generalized to ANY map that
\* is DeepestKnownCorrectP for m (in particular the assembly over the
\* priors' MemoP records): the entry's message for a signer s never sits
\* strictly below another s-signed message of the exclusive history, since
\* that message's own chain would be strictly deeper -- contradicting the
\* entry's depth-maximality.  The depths involved are the ordinary semantic
\* DeepestKnownDepth values, so the canonical invariant supplies everything
\* about the competitor.
EXTENDS MemoPDefs, DeepestKnownInv, TranSubMessages
LOCAL INSTANCE TLAPS

LEMMA MemoPDKMaximal ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         NEW m \in Messages, NEW dk,
         DeepestKnownCorrectP(m, dk),
         NEW s \in DOMAIN dk,
         NEW y \in TranExclusive(m), Sig(y) = s,
         dk[s][2].id \in TranExclusive(y)
  PROVE FALSE
<1> DEFINE zz == dk[s][2].id
<1>e. /\ Sig(zz) = s
      /\ dk[s][1] \in Nat
      /\ dk[s] = <<DeepestKnownDepth(s, zz), dk[s][2]>>
  BY DEF DeepestKnownCorrectP
<1>n. dk[s][1] = DeepestKnownDepth(s, zz)
  <2>1. <<DeepestKnownDepth(s, zz), dk[s][2]>>[1] = DeepestKnownDepth(s, zz)
    OBVIOUS
  <2> QED BY <1>e, <2>1
<1>max. \A w \in TranExclusive(m) : Sig(w) = s =>
          DeepestKnownDepth(s, w) <= dk[s][1]
  BY DEF DeepestKnownCorrectP
<1>yM. y \in Messages  BY TranSubMessages DEF TranExclusive
<1>invY. DeepestKnownInvariant(y)  BY <1>yM, DeepestKnownInv
<1>sdomY. s \in DOMAIN DeepestKnown(y)
  <2>1. s \in SigS(TranExclusive(y))  BY <1>e DEF SigS
  <2> QED BY <2>1, <1>invY DEF DeepestKnownInvariant
<1>dy. DeepestKnownDepth(s, y) = DeepestKnown(y)[s][1] + 1
  BY <1>sdomY DEF DeepestKnownDepth
<1>deepY. DeepestKnownDepth(s, zz) <= DeepestKnown(y)[s][1]
  BY <1>invY, <1>sdomY, <1>e DEF DeepestKnownInvariant
<1>tyY. DeepestKnown(y)[s][1] \in Nat
  BY <1>invY, <1>sdomY DEF DeepestKnownInvariant
<1>deepM. DeepestKnownDepth(s, y) <= dk[s][1]  BY <1>max
<1> QED BY <1>dy, <1>deepY, <1>tyY, <1>deepM, <1>n, <1>e, SMT
=============================================================================
