----------------------------- MODULE DeepestKnownU -----------------------------
\* Plan step (a) toward CWellFormedRec: the (pr, U)-virtualized
\* DeepestKnownStep.  For a FINITE prior set pr \subseteq Messages -- with no
\* assembling message x -- the deepestknown assembly over pr's digests is
\* correct for U := UNION {Tran(p) : p \in pr} (the exclusive closure the
\* candidate WOULD have, by CBuiltTran).  Adapted from DeepestKnownStep: x
\* entered that proof only through TranExclusive(x) (replaced by U wholesale)
\* and through Tran(x)'s finiteness (pr finite is now a hypothesis); the
\* per-member facts come from DeepestKnownInv, since members ARE Messages.
EXTENDS DigestUDefs, DigestRec, DeepestKnownInv, TranSubMessages,
        FiniteSetTheorems, PairFstMaxExists
LOCAL INSTANCE TLAPS

LEMMA DeepestKnownU ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         NEW pr, pr \subseteq Messages, IsFiniteSet(pr)
  PROVE DeepestKnownCorrectU(UNION {Tran(p) : p \in pr},
                             DeepestKnownAssemble({Digest(p) : p \in pr}))
<1> DEFINE R == pr
<1> DEFINE recs == {Digest(p) : p \in R}
<1> DEFINE dka == DeepestKnownAssemble(recs)
<1> DEFINE UU == UNION {Tran(p) : p \in R}
<1>ih. \A p \in R : DeepestKnownInvariant(p)  BY DeepestKnownInv
<1>rM. R \subseteq Messages  OBVIOUS
<1>texP. \A p \in R : Tran(p) \subseteq UU  OBVIOUS
<1>texPP. \A p \in R : TranExclusive(p) \subseteq UU
  BY <1>texP DEF TranExclusive
<1>pTE. \A p \in R : p \in UU
  <2> SUFFICES ASSUME NEW p \in R PROVE p \in UU  OBVIOUS
  <2>1. p \in Tran(p)  BY DEF Tran
  <2> QED BY <2>1
<1>idp. \A p \in R : /\ Digest(p).id = p
                     /\ Digest(p).deepestknown = DeepestKnown(p)
  <2> SUFFICES ASSUME NEW p \in R
      PROVE /\ Digest(p).id = p
            /\ Digest(p).deepestknown = DeepestKnown(p)
    OBVIOUS
  <2>1. p \in Messages  BY <1>rM
  <2>2. Digest(p) = DigestR(p, {Digest(q) : q \in Refs(p)})
    BY <2>1, DigestRec
  <2> QED BY <2>2 DEF DigestR, DeepestKnown
<1>dom0. DOMAIN dka = DeepestKnownSigners(recs)
  BY DEF DeepestKnownAssemble
<1>ihdom. \A p \in R : DOMAIN DeepestKnown(p) = SigS(TranExclusive(p))
  BY <1>ih DEF DeepestKnownInvariant
\* ------------------------------------------------------------------ domain
<1>sigid. {Sig(rc.id) : rc \in recs} = {Sig(p) : p \in R}
  <2>1. \A p \in R : Sig(Digest(p).id) = Sig(p)  BY <1>idp
  <2>sub. {Sig(rc.id) : rc \in recs} \subseteq {Sig(p) : p \in R}
    <3> SUFFICES ASSUME NEW rc \in recs
        PROVE Sig(rc.id) \in {Sig(p) : p \in R}  OBVIOUS
    <3>1. PICK p \in R : rc = Digest(p)  OBVIOUS
    <3> QED BY <3>1, <2>1
  <2>sup. {Sig(p) : p \in R} \subseteq {Sig(rc.id) : rc \in recs}
    <3> SUFFICES ASSUME NEW p \in R
        PROVE Sig(p) \in {Sig(rc.id) : rc \in recs}  OBVIOUS
    <3>1. Digest(p) \in recs  OBVIOUS
    <3> QED BY <3>1, <2>1
  <2> QED BY <2>sub, <2>sup
<1>dkdom. UNION {DOMAIN rc.deepestknown : rc \in recs}
            = UNION {SigS(TranExclusive(p)) : p \in R}
  <2>1. \A p \in R : DOMAIN Digest(p).deepestknown = SigS(TranExclusive(p))
    BY <1>idp, <1>ihdom
  <2>sub. UNION {DOMAIN rc.deepestknown : rc \in recs}
            \subseteq UNION {SigS(TranExclusive(p)) : p \in R}
    <3> SUFFICES ASSUME NEW s \in UNION {DOMAIN rc.deepestknown : rc \in recs}
        PROVE s \in UNION {SigS(TranExclusive(p)) : p \in R}  OBVIOUS
    <3>1. PICK rc \in recs : s \in DOMAIN rc.deepestknown  OBVIOUS
    <3>2. PICK p \in R : rc = Digest(p)  OBVIOUS
    <3>3. s \in SigS(TranExclusive(p))  BY <3>1, <3>2, <2>1
    <3> QED BY <3>3
  <2>sup. UNION {SigS(TranExclusive(p)) : p \in R}
            \subseteq UNION {DOMAIN rc.deepestknown : rc \in recs}
    <3> SUFFICES ASSUME NEW p \in R, NEW s \in SigS(TranExclusive(p))
        PROVE s \in UNION {DOMAIN rc.deepestknown : rc \in recs}  OBVIOUS
    <3>1. Digest(p) \in recs  OBVIOUS
    <3>2. s \in DOMAIN Digest(p).deepestknown  BY <2>1
    <3> QED BY <3>1, <3>2
  <2> QED BY <2>sub, <2>sup
<1>sigTE. SigS(UU)
            = {Sig(p) : p \in R} \cup UNION {SigS(TranExclusive(p)) : p \in R}
  <2>sub. SigS(UU)
            \subseteq {Sig(p) : p \in R}
                        \cup UNION {SigS(TranExclusive(p)) : p \in R}
    <3> SUFFICES ASSUME NEW s \in SigS(UU)
        PROVE s \in {Sig(p) : p \in R}
                     \cup UNION {SigS(TranExclusive(p)) : p \in R}
      OBVIOUS
    <3>w. PICK w \in UU : s = Sig(w)  BY DEF SigS
    <3>p. PICK p \in R : w \in Tran(p)  OBVIOUS
    <3>a. CASE w = p
      <4> QED BY <3>w, <3>p, <3>a
    <3>b. CASE w # p
      <4>1. w \in TranExclusive(p)  BY <3>p, <3>b DEF TranExclusive
      <4>2. s \in SigS(TranExclusive(p))  BY <3>w, <4>1 DEF SigS
      <4> QED BY <3>p, <4>2
    <3> QED BY <3>a, <3>b
  <2>sup. {Sig(p) : p \in R} \cup UNION {SigS(TranExclusive(p)) : p \in R}
            \subseteq SigS(UU)
    <3>1. \A p \in R : Sig(p) \in SigS(UU)
      BY <1>pTE DEF SigS
    <3>2. \A p \in R : SigS(TranExclusive(p)) \subseteq SigS(UU)
      BY <1>texPP DEF SigS
    <3> QED BY <3>1, <3>2
  <2> QED BY <2>sub, <2>sup
<1>dom. DOMAIN dka = SigS(UU)
  BY <1>dom0, <1>sigid, <1>dkdom, <1>sigTE DEF DeepestKnownSigners
\* ------------------------------------------------------------------ per-s
<1>main. \A s \in DOMAIN dka :
       /\ dka[s][2] = Digest(dka[s][2].id)
       /\ dka[s][2].id \in UU
       /\ Sig(dka[s][2].id) = s
       /\ dka[s][1] \in Nat
       /\ dka[s]
            = <<DeepestKnownDepth(s, dka[s][2].id),
                dka[s][2]>>
       /\ \A w \in UU : Sig(w) = s =>
            /\ DeepestKnownDepth(s, w) \in Nat
            /\ DeepestKnownDepth(s, w) <= dka[s][1]
  <2> SUFFICES ASSUME NEW s \in DOMAIN dka
      PROVE /\ dka[s][2] = Digest(dka[s][2].id)
            /\ dka[s][2].id \in UU
            /\ Sig(dka[s][2].id) = s
            /\ dka[s][1] \in Nat
            /\ dka[s]
                 = <<DeepestKnownDepth(s, dka[s][2].id),
                     dka[s][2]>>
            /\ \A w \in UU : Sig(w) = s =>
                 /\ DeepestKnownDepth(s, w) \in Nat
                 /\ DeepestKnownDepth(s, w) <= dka[s][1]
    OBVIOUS
  <2> DEFINE C == DeepestKnownCandidates(s, recs)
  <2>sD. s \in DeepestKnownSigners(recs)  BY <1>dom0
  <2>ent. dka[s]
            = CHOOSE c \in DeepestKnownCandidates(s, recs) :
                \A c2 \in DeepestKnownCandidates(s, recs) : c[1] >= c2[1]
    BY <2>sD DEF DeepestKnownAssemble
  <2>natR. \A p \in R : DeepestKnownDepth(s, p) \in Nat
    <3> SUFFICES ASSUME NEW p \in R PROVE DeepestKnownDepth(s, p) \in Nat
      OBVIOUS
    <3>a. CASE s \in DOMAIN DeepestKnown(p)
      <4>1. DeepestKnown(p)[s][1] \in Nat
        BY <1>ih, <3>a DEF DeepestKnownInvariant
      <4> QED BY <4>1, <3>a DEF DeepestKnownDepth
    <3>b. CASE s \notin DOMAIN DeepestKnown(p)
      <4> QED BY <3>b DEF DeepestKnownDepth
    <3> QED BY <3>a, <3>b
  <2>scand. \A p \in R : Sig(p) = s =>
       DeepestKnownSignerCand(s, Digest(p))
         = <<DeepestKnownDepth(s, p), Digest(p)>>
    <3> SUFFICES ASSUME NEW p \in R, Sig(p) = s
        PROVE DeepestKnownSignerCand(s, Digest(p))
                = <<DeepestKnownDepth(s, p), Digest(p)>>
      OBVIOUS
    <3>1. Digest(p).deepestknown = DeepestKnown(p)  BY <1>idp
    <3> QED BY <3>1 DEF DeepestKnownSignerCand, DeepestKnownDepth
  <2>candS. \A p \in R : Sig(p) = s =>
              DeepestKnownSignerCand(s, Digest(p)) \in C
    <3> SUFFICES ASSUME NEW p \in R, Sig(p) = s
        PROVE DeepestKnownSignerCand(s, Digest(p)) \in C
      OBVIOUS
    <3>1. Digest(p) \in recs  OBVIOUS
    <3>2. Sig(Digest(p).id) = s  BY <1>idp
    <3>3. Digest(p) \in {y \in recs : Sig(y.id) = s}
      BY <3>1, <3>2
    <3> QED BY <3>3 DEF DeepestKnownCandidates
  <2>candC. \A p \in R : (Sig(p) # s /\ s \in DOMAIN DeepestKnown(p)) =>
              DeepestKnown(p)[s] \in C
    <3> SUFFICES ASSUME NEW p \in R, Sig(p) # s, s \in DOMAIN DeepestKnown(p)
        PROVE DeepestKnown(p)[s] \in C
      OBVIOUS
    <3>1. Digest(p) \in recs  OBVIOUS
    <3>2. Sig(Digest(p).id) # s
            /\ s \in DOMAIN Digest(p).deepestknown
      BY <1>idp
    <3>3. Digest(p)
            \in {y \in recs : Sig(y.id) # s /\ s \in DOMAIN y.deepestknown}
      BY <3>1, <3>2
    <3>4. DeepestKnownCarrierCand(s, Digest(p)) = DeepestKnown(p)[s]
      BY <1>idp DEF DeepestKnownCarrierCand
    <3> QED BY <3>3, <3>4 DEF DeepestKnownCandidates
  <2>shape. \A c \in C : /\ c[2] = Digest(c[2].id)
                         /\ c[2].id \in UU
                         /\ Sig(c[2].id) = s
                         /\ c[1] \in Nat
                         /\ c = <<DeepestKnownDepth(s, c[2].id), c[2]>>
    <3> SUFFICES ASSUME NEW c \in C
        PROVE /\ c[2] = Digest(c[2].id)
              /\ c[2].id \in UU
              /\ Sig(c[2].id) = s
              /\ c[1] \in Nat
              /\ c = <<DeepestKnownDepth(s, c[2].id), c[2]>>
      OBVIOUS
    <3>split.
        \/ c \in {DeepestKnownSignerCand(s, rc) :
                    rc \in {y \in recs : Sig(y.id) = s}}
        \/ c \in {DeepestKnownCarrierCand(s, rc) :
                    rc \in {y \in recs :
                              Sig(y.id) # s /\ s \in DOMAIN y.deepestknown}}
      BY DEF DeepestKnownCandidates
    <3>a. CASE c \in {DeepestKnownSignerCand(s, rc) :
                        rc \in {y \in recs : Sig(y.id) = s}}
      <4>rc. PICK rc \in {y \in recs : Sig(y.id) = s} :
               c = DeepestKnownSignerCand(s, rc)
        BY <3>a
      <4>p. PICK p \in R : rc = Digest(p)  BY <4>rc
      <4>sig. Sig(p) = s  BY <4>rc, <4>p, <1>idp
      <4>ceq. c = <<DeepestKnownDepth(s, p), Digest(p)>>
        BY <4>rc, <4>p, <4>sig, <2>scand
      <4>id. Digest(p).id = p  BY <1>idp
      <4>nat. DeepestKnownDepth(s, p) \in Nat  BY <2>natR
      <4>tex. p \in UU  BY <1>pTE
      <4> QED BY <4>ceq, <4>id, <4>nat, <4>tex, <4>sig
    <3>b. CASE c \in {DeepestKnownCarrierCand(s, rc) :
                        rc \in {y \in recs :
                                  Sig(y.id) # s /\ s \in DOMAIN y.deepestknown}}
      <4>rc. PICK rc \in {y \in recs :
                            Sig(y.id) # s /\ s \in DOMAIN y.deepestknown} :
               c = DeepestKnownCarrierCand(s, rc)
        BY <3>b
      <4>p. PICK p \in R : rc = Digest(p)  BY <4>rc
      <4>c2. c = DeepestKnown(p)[s] /\ s \in DOMAIN DeepestKnown(p)
        BY <4>rc, <4>p, <1>idp DEF DeepestKnownCarrierCand
      <4>ihp. DeepestKnownInvariant(p)  BY <1>ih
      <4>facts. /\ DeepestKnown(p)[s][2] = Digest(DeepestKnown(p)[s][2].id)
                /\ DeepestKnown(p)[s][2].id \in TranExclusive(p)
                /\ Sig(DeepestKnown(p)[s][2].id) = s
                /\ DeepestKnown(p)[s][1] \in Nat
                /\ DeepestKnown(p)[s]
                     = <<DeepestKnownDepth(s, DeepestKnown(p)[s][2].id),
                         DeepestKnown(p)[s][2]>>
        BY <4>ihp, <4>c2 DEF DeepestKnownInvariant
      <4>tex. DeepestKnown(p)[s][2].id \in UU
        BY <4>facts, <1>texPP
      <4> QED BY <4>c2, <4>facts, <4>tex
    <3> QED BY <3>split, <3>a, <3>b
  <2>ne. C # {}
    <3>1. \/ s \in {Sig(rc.id) : rc \in recs}
          \/ s \in UNION {DOMAIN rc.deepestknown : rc \in recs}
      BY <2>sD DEF DeepestKnownSigners
    <3>a. CASE s \in {Sig(rc.id) : rc \in recs}
      <4>1. s \in {Sig(p) : p \in R}  BY <3>a, <1>sigid
      <4>2. PICK p \in R : s = Sig(p)  BY <4>1
      <4> QED BY <4>2, <2>candS
    <3>b. CASE s \in UNION {DOMAIN rc.deepestknown : rc \in recs}
      <4>1. s \in UNION {SigS(TranExclusive(p)) : p \in R}  BY <3>b, <1>dkdom
      <4>2. PICK p \in R : s \in SigS(TranExclusive(p))  BY <4>1
      <4>3. s \in DOMAIN DeepestKnown(p)  BY <4>2, <1>ihdom
      <4>a. CASE Sig(p) = s
        <5> QED BY <4>a, <2>candS
      <4>b. CASE Sig(p) # s
        <5> QED BY <4>3, <4>b, <2>candC
      <4> QED BY <4>a, <4>b
    <3> QED BY <3>1, <3>a, <3>b
  <2>fin. IsFiniteSet(C)
    <3>fR. IsFiniteSet(R)  OBVIOUS
    <3>frecs. IsFiniteSet(recs)  BY <3>fR, FS_Image
    <3>f1. IsFiniteSet({y \in recs : Sig(y.id) = s})
      BY <3>frecs, FS_Subset
    <3>f2. IsFiniteSet({y \in recs :
                          Sig(y.id) # s /\ s \in DOMAIN y.deepestknown})
      BY <3>frecs, FS_Subset
    <3>fS. IsFiniteSet({DeepestKnownSignerCand(s, rc) :
                          rc \in {y \in recs : Sig(y.id) = s}})
      BY <3>f1, FS_Image
    <3>fC. IsFiniteSet({DeepestKnownCarrierCand(s, rc) :
                          rc \in {y \in recs :
                                    Sig(y.id) # s
                                    /\ s \in DOMAIN y.deepestknown}})
      BY <3>f2, FS_Image
    <3> QED BY <3>fS, <3>fC, FS_Union DEF DeepestKnownCandidates
  <2>maxE. \E c \in C : \A c2 \in C : c[1] >= c2[1]
    <3>1. \A c \in C : c[1] \in Nat  BY <2>shape
    <3> QED BY <2>fin, <2>ne, <3>1, PairFstMaxExists
  <2>win. /\ dka[s] \in C
          /\ \A c2 \in C : dka[s][1] >= c2[1]
    BY <2>ent, <2>maxE
  <2>c12345. /\ dka[s][2] = Digest(dka[s][2].id)
             /\ dka[s][2].id \in UU
             /\ Sig(dka[s][2].id) = s
             /\ dka[s][1] \in Nat
             /\ dka[s]
                  = <<DeepestKnownDepth(s, dka[s][2].id),
                      dka[s][2]>>
    BY <2>win, <2>shape
  <2>deep. \A w \in UU : Sig(w) = s =>
             /\ DeepestKnownDepth(s, w) \in Nat
             /\ DeepestKnownDepth(s, w) <= dka[s][1]
    <3> SUFFICES ASSUME NEW w \in UU, Sig(w) = s
        PROVE /\ DeepestKnownDepth(s, w) \in Nat
              /\ DeepestKnownDepth(s, w) <= dka[s][1]
      OBVIOUS
    <3>p. PICK p \in R : w \in Tran(p)  OBVIOUS
    <3>wtyp. dka[s][1] \in Nat  BY <2>c12345
    <3>a. CASE w = p
      <4>sig. Sig(p) = s  BY <3>a
      <4>c. DeepestKnownSignerCand(s, Digest(p)) \in C
        BY <4>sig, <2>candS
      <4>ceq. DeepestKnownSignerCand(s, Digest(p))
                = <<DeepestKnownDepth(s, p), Digest(p)>>
        BY <4>sig, <2>scand
      <4>le. dka[s][1] >= DeepestKnownDepth(s, p)
        <5>1. <<DeepestKnownDepth(s, p), Digest(p)>>[1]
                = DeepestKnownDepth(s, p)
          OBVIOUS
        <5> QED BY <4>c, <4>ceq, <5>1, <2>win
      <4> QED BY <3>a, <4>le, <2>natR, <3>wtyp
    <3>b. CASE w # p
      <4>wTE. w \in TranExclusive(p)  BY <3>p, <3>b DEF TranExclusive
      <4>ihp. DeepestKnownInvariant(p)  BY <1>ih
      <4>sdom. s \in DOMAIN DeepestKnown(p)
        <5>1. s \in SigS(TranExclusive(p))  BY <4>wTE DEF SigS
        <5> QED BY <5>1, <1>ihdom
      <4>bound. /\ DeepestKnownDepth(s, w) \in Nat
                /\ DeepestKnownDepth(s, w) <= DeepestKnown(p)[s][1]
        BY <4>ihp, <4>sdom, <4>wTE DEF DeepestKnownInvariant
      <4>ptyp. DeepestKnown(p)[s][1] \in Nat
        BY <4>ihp, <4>sdom DEF DeepestKnownInvariant
      <4>a. CASE Sig(p) = s
        <5>c. DeepestKnownSignerCand(s, Digest(p)) \in C
          BY <4>a, <2>candS
        <5>ceq. DeepestKnownSignerCand(s, Digest(p))
                  = <<DeepestKnownDepth(s, p), Digest(p)>>
          BY <4>a, <2>scand
        <5>dp. DeepestKnownDepth(s, p) = DeepestKnown(p)[s][1] + 1
          BY <4>sdom DEF DeepestKnownDepth
        <5>le. dka[s][1] >= DeepestKnownDepth(s, p)
          <6>1. <<DeepestKnownDepth(s, p), Digest(p)>>[1]
                  = DeepestKnownDepth(s, p)
            OBVIOUS
          <6> QED BY <5>c, <5>ceq, <6>1, <2>win
        <5> QED BY <4>bound, <5>dp, <5>le, <4>ptyp, <3>wtyp, SMT
      <4>b. CASE Sig(p) # s
        <5>c. DeepestKnown(p)[s] \in C  BY <4>b, <4>sdom, <2>candC
        <5>le. dka[s][1] >= DeepestKnown(p)[s][1]
          BY <5>c, <2>win
        <5> QED BY <4>bound, <5>le, <4>ptyp, <3>wtyp, SMT
      <4> QED BY <4>a, <4>b
    <3> QED BY <3>a, <3>b
  <2> QED BY <2>c12345, <2>deep
<1> QED BY <1>dom, <1>main DEF DeepestKnownCorrectU
=============================================================================
