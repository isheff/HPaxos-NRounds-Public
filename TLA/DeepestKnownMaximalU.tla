-------------------------- MODULE DeepestKnownMaximalU --------------------------
\* U-parameterized version of DeepestKnownMaximalG: any deepestknown map that
\* is CorrectU for a message set UU has entries maximal among same-signed
\* members -- an entry sitting strictly below a same-signed member y would
\* contradict y's own field invariant (the chain through y is one longer).
EXTENDS MemoUDefs, DeepestKnownInv, TranSubMessages
LOCAL INSTANCE TLAPS

LEMMA DeepestKnownMaximalU ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         NEW UU, UU \subseteq Messages,
         NEW dkm, DeepestKnownCorrectU(UU, dkm),
         NEW s \in DOMAIN dkm,
         NEW y \in UU, Sig(y) = s,
         dkm[s][2].id \in TranExclusive(y)
  PROVE FALSE
<1>inv. DeepestKnownCorrectU(UU, dkm)  OBVIOUS
<1> DEFINE zz == dkm[s][2].id
<1>e. /\ Sig(zz) = s
      /\ dkm[s][1] \in Nat
      /\ dkm[s] = <<DeepestKnownDepth(s, zz), dkm[s][2]>>
  BY <1>inv DEF DeepestKnownCorrectU
<1>n. dkm[s][1] = DeepestKnownDepth(s, zz)  BY <1>e
<1>max. \A w \in UU : Sig(w) = s =>
          DeepestKnownDepth(s, w) <= dkm[s][1]
  BY <1>inv DEF DeepestKnownCorrectU
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
<1>deepM. DeepestKnownDepth(s, y) <= dkm[s][1]  BY <1>max
<1> QED BY <1>dy, <1>deepY, <1>tyY, <1>deepM, <1>n, <1>e, SMT
=============================================================================
