------------------------- MODULE DeepestKnownPrev -------------------------
\*   DeepestKnownInv, PrevDom, TranSubMessages -> cited lemmas
\*   TLAPS -> SMT; proof-only
EXTENDS RecursiveWellFormed, DeepestKnownInv, PrevDom, TranSubMessages
LOCAL INSTANCE TLAPS

\* deepestknown has an entry for m's own signer exactly when m has a
\* previous message, and that entry's message IS a previous message: a
\* deepest same-signer ancestor cannot sit strictly below another same-
\* signer message y (y would have a strictly longer chain), so it is
\* maximal among same-signer ancestors -- the defining property of Prev.
LEMMA DeepestKnownPrev ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         NEW m \in Messages
  PROVE /\ (Sig(m) \in DOMAIN DeepestKnown(m)) <=> (Prev(m) # {})
        /\ (Sig(m) \in DOMAIN DeepestKnown(m)) =>
             DeepestKnown(m)[Sig(m)][2].id \in Prev(m)
<1>inv. DeepestKnownInvariant(m)  BY DeepestKnownInv
<1>dom. DOMAIN DeepestKnown(m) = SigS(TranExclusive(m))
  BY <1>inv DEF DeepestKnownInvariant
<1>fwd. (Sig(m) \in DOMAIN DeepestKnown(m)) => (Prev(m) # {})
  <2>1. CASE Sig(m) \in DOMAIN DeepestKnown(m)
    <3>1. Sig(m) \in SigS(TranExclusive(m))  BY <2>1, <1>dom
    <3>2. PICK z \in TranExclusive(m) : Sig(z) = Sig(m)  BY <3>1 DEF SigS
    <3>3. \E q \in Prev(m) : z \in Tran(q)  BY <3>2, PrevDom
    <3> QED BY <3>3
  <2> QED BY <2>1
<1>bwd. (Prev(m) # {}) => (Sig(m) \in DOMAIN DeepestKnown(m))
  <2>1. CASE Prev(m) # {}
    <3>1. PICK q \in Prev(m) : TRUE  BY <2>1
    <3>2. q \in TranExclusive(m) /\ Sig(q) = Sig(m)  BY <3>1 DEF Prev
    <3>3. Sig(m) \in SigS(TranExclusive(m))  BY <3>2 DEF SigS
    <3> QED BY <3>3, <1>dom
  <2> QED BY <2>1
<1>main. \A s \in DOMAIN DeepestKnown(m) :
           s = Sig(m) => DeepestKnown(m)[s][2].id \in Prev(m)
  <2> SUFFICES ASSUME NEW s \in DOMAIN DeepestKnown(m), s = Sig(m)
      PROVE DeepestKnown(m)[s][2].id \in Prev(m)
    OBVIOUS
  <2> DEFINE zz == DeepestKnown(m)[s][2].id
  <2>e. /\ zz \in TranExclusive(m)
        /\ Sig(zz) = s
        /\ DeepestKnown(m)[s][1] \in Nat
        /\ DeepestKnown(m)[s] = <<DeepestKnownDepth(s, zz),
                                  DeepestKnown(m)[s][2]>>
    BY <1>inv DEF DeepestKnownInvariant
  <2>n. DeepestKnown(m)[s][1] = DeepestKnownDepth(s, zz)  BY <2>e
  <2>max. \A w \in TranExclusive(m) : Sig(w) = s =>
            DeepestKnownDepth(s, w) <= DeepestKnown(m)[s][1]
    BY <1>inv DEF DeepestKnownInvariant
  <2>prev. \A y \in TranExclusive(m) : zz \in TranExclusive(y) => Sig(zz) # Sig(y)
    <3> SUFFICES ASSUME NEW y \in TranExclusive(m),
                        zz \in TranExclusive(y),
                        Sig(zz) = Sig(y)
        PROVE FALSE
      OBVIOUS
    <3>ysig. Sig(y) = s  BY <2>e
    <3>yM. y \in Messages  BY TranSubMessages DEF TranExclusive
    <3>invY. DeepestKnownInvariant(y)  BY <3>yM, DeepestKnownInv
    <3>sdomY. s \in DOMAIN DeepestKnown(y)
      <4>1. s \in SigS(TranExclusive(y))  BY <2>e DEF SigS
      <4> QED BY <4>1, <3>invY DEF DeepestKnownInvariant
    <3>dy. DeepestKnownDepth(s, y) = DeepestKnown(y)[s][1] + 1
      BY <3>sdomY DEF DeepestKnownDepth
    <3>deepY. DeepestKnownDepth(s, zz) <= DeepestKnown(y)[s][1]
      BY <3>invY, <3>sdomY, <2>e DEF DeepestKnownInvariant
    <3>tyY. DeepestKnown(y)[s][1] \in Nat
      BY <3>invY, <3>sdomY DEF DeepestKnownInvariant
    <3>deepM. DeepestKnownDepth(s, y) <= DeepestKnown(m)[s][1]
      BY <2>max, <3>ysig
    <3> QED BY <3>dy, <3>deepY, <3>tyY, <3>deepM, <2>n, <2>e, SMT
  <2> QED BY <2>e, <2>prev DEF Prev
<1> QED BY <1>fwd, <1>bwd, <1>main
====================================================================
