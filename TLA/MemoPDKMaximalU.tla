---------------------------- MODULE MemoPDKMaximalU ----------------------------
\* U-parameterized MemoPDKMaximal: an entry of a DeepestKnownCorrectUP map
\* never sits strictly below a same-signed member of UU, since that member's
\* own canonical chain would be one deeper -- contradicting the entry's
\* depth-maximality over UU.  The competitor's side of the comparison is
\* entirely canonical (DeepestKnownInv), because depths are semantic.
EXTENDS MemoPUDefs, DeepestKnownInv, TranSubMessages
LOCAL INSTANCE TLAPS

LEMMA MemoPDKMaximalU ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         NEW UU, UU \subseteq Messages,
         NEW dk, DeepestKnownCorrectUP(UU, dk),
         NEW s \in DOMAIN dk,
         NEW y \in UU, Sig(y) = s,
         dk[s][2].id \in TranExclusive(y)
  PROVE FALSE
<1> DEFINE zz == dk[s][2].id
<1>e. /\ Sig(zz) = s
      /\ dk[s][1] \in Nat
      /\ dk[s] = <<DeepestKnownDepth(s, zz), dk[s][2]>>
  BY DEF DeepestKnownCorrectUP
<1>n. dk[s][1] = DeepestKnownDepth(s, zz)
  <2>1. <<DeepestKnownDepth(s, zz), dk[s][2]>>[1] = DeepestKnownDepth(s, zz)
    OBVIOUS
  <2> QED BY <1>e, <2>1
<1>max. \A w \in UU : Sig(w) = s => DeepestKnownDepth(s, w) <= dk[s][1]
  BY DEF DeepestKnownCorrectUP
<1>yM. y \in Messages  OBVIOUS
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
