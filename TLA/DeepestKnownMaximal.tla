----------------------- MODULE DeepestKnownMaximal -----------------------
\*   DeepestKnownInv, TranSubMessages -> cited lemmas
\*   TLAPS -> SMT; proof-only
EXTENDS RecursiveWellFormed, DeepestKnownInv, TranSubMessages
LOCAL INSTANCE TLAPS

\* The deepestknown entry's message for any signer s is maximal among
\* s-signed messages in the exclusive history: it never sits strictly below
\* another s-signed message y there (y's chain would be strictly longer,
\* contradicting the entry's depth-maximality). Generalizes the maximality
\* step inside DeepestKnownPrev from s = Sig(m) to every s in the domain.
LEMMA DeepestKnownMaximal ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         NEW m \in Messages, NEW s \in DOMAIN DeepestKnown(m),
         NEW y \in TranExclusive(m), Sig(y) = s,
         DeepestKnown(m)[s][2].id \in TranExclusive(y)
  PROVE FALSE
<1>inv. DeepestKnownInvariant(m)  BY DeepestKnownInv
<1> DEFINE zz == DeepestKnown(m)[s][2].id
<1>e. /\ Sig(zz) = s
      /\ DeepestKnown(m)[s][1] \in Nat
      /\ DeepestKnown(m)[s] = <<DeepestKnownDepth(s, zz),
                                DeepestKnown(m)[s][2]>>
  BY <1>inv DEF DeepestKnownInvariant
<1>n. DeepestKnown(m)[s][1] = DeepestKnownDepth(s, zz)  BY <1>e
<1>max. \A w \in TranExclusive(m) : Sig(w) = s =>
          DeepestKnownDepth(s, w) <= DeepestKnown(m)[s][1]
  BY <1>inv DEF DeepestKnownInvariant
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
<1>deepM. DeepestKnownDepth(s, y) <= DeepestKnown(m)[s][1]  BY <1>max
<1> QED BY <1>dy, <1>deepY, <1>tyY, <1>deepM, <1>n, <1>e, SMT
====================================================================
