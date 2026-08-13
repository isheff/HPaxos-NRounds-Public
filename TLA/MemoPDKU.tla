-------------------------------- MODULE MemoPDKU --------------------------------
\* The (pr, U)-virtualized MemoPDKStep: for a FINITE prior set pr of real
\* messages -- with no assembling message yet -- the deepestknown assembly
\* over the priors' MemoP records is P-correct for UU := UNION {Tran(p) :
\* p \in pr}, the exclusive closure the candidate WOULD have (CBuiltTran).
\*
\* Adapted from MemoPDKStep by the same (pr, U)-virtualization that carries
\* DeepestKnownStep to a prior set: x entered only through TranExclusive(x)
\* (replaced by UU
\* wholesale) and through Tran(x)'s finiteness (pr finite is now a
\* hypothesis).  Member facts come from MemoPGoodInv, since the priors are
\* real messages; the depth bridge to the canonical DeepestKnown is the
\* same attainment-plus-maximality argument as in MemoPDKStep.
EXTENDS MemoPUDefs, MemoPDefs, MemoPGoodInv, DeepestKnownInv, TranSubMessages,
        FiniteSetTheorems, PairFstMaxExists, CFields
LOCAL INSTANCE TLAPS

LEMMA MemoPDKU ==
  ASSUME MessageInterfaceAssumptions,
         LearnersMightAgree, ValidLearnerGraphAssumption,
         MessageInterface = CMI,
         NEW pr, pr \subseteq CMessages, IsFiniteSet(pr)
  PROVE DeepestKnownCorrectUP(UNION {Tran(p) : p \in pr},
                              DeepestKnownAssemble({MemoP(p) : p \in pr}))
<1> DEFINE rP == {MemoP(q) : q \in pr}
<1> DEFINE dka == DeepestKnownAssemble(rP)
<1> DEFINE UU == UNION {Tran(p) : p \in pr}
<1> DEFINE DKP(q) == MemoP(q).deepestknown
\* ------------------------------------------------------------------ prelude
<1>tok. TypeOKMessageInterface  BY DEF MessageInterfaceAssumptions
<1>tf. TranFinite  BY DEF MessageInterfaceAssumptions
<1>tt. TranTrans  BY DEF MessageInterfaceAssumptions
<1>ta. TranAcyclic  BY DEF MessageInterfaceAssumptions
<1>anp. AlwaysAProposal  BY DEF MessageInterfaceAssumptions
<1>prMsg. pr \subseteq Messages  BY CFields
<1>ihq. \A q \in pr : MemoPGood(q)  BY MemoPGoodInv
<1>texP. \A q \in pr : Tran(q) \subseteq UU  OBVIOUS
<1>texPP. \A q \in pr : TranExclusive(q) \subseteq UU
  BY <1>texP DEF TranExclusive
<1>pTE. \A q \in pr : q \in UU
  <2> SUFFICES ASSUME NEW q \in pr PROVE q \in UU  OBVIOUS
  <2>1. q \in Tran(q)  BY DEF Tran
  <2> QED BY <2>1
<1>teM. UU \subseteq Messages
  <2> SUFFICES ASSUME NEW w \in UU PROVE w \in Messages  OBVIOUS
  <2>1. PICK q \in pr : w \in Tran(q)  OBVIOUS
  <2>2. q \in Messages  BY <1>prMsg
  <2> QED BY <2>1, <2>2, <1>tok, TranSubMessages
\* ------------------------------------- member facts (good + canonical invariant)
<1>idp. \A q \in pr : MemoP(q).id = q  BY <1>ihq DEF MemoPGood
<1>ihP. \A q \in pr : DeepestKnownCorrectP(q, DKP(q))
  BY <1>ihq DEF MemoPGood
<1>ihdomP. \A q \in pr : DOMAIN DKP(q) = SigS(TranExclusive(q))
  BY <1>ihP DEF DeepestKnownCorrectP
<1>ihC. \A q \in pr : DeepestKnownInvariant(q)
  BY <1>prMsg, <1>tok, <1>tt, <1>tf, <1>ta, DeepestKnownInv
<1>ihdomC. \A q \in pr : DOMAIN DeepestKnown(q) = SigS(TranExclusive(q))
  BY <1>ihC DEF DeepestKnownInvariant
\* -------------------------------------------------------------- depth bridge
<1>bridge. \A q \in pr : \A s \in DOMAIN DKP(q) :
             DKP(q)[s][1] = DeepestKnown(q)[s][1]
  <2> SUFFICES ASSUME NEW q \in pr, NEW s \in DOMAIN DKP(q)
      PROVE DKP(q)[s][1] = DeepestKnown(q)[s][1]
    OBVIOUS
  <2>sC. s \in DOMAIN DeepestKnown(q)  BY <1>ihdomP, <1>ihdomC
  <2>pf. /\ DKP(q)[s][1] \in Nat
         /\ DKP(q)[s]
              = <<DeepestKnownDepth(s, DKP(q)[s][2].id), DKP(q)[s][2]>>
         /\ DKP(q)[s][2].id \in TranExclusive(q)
         /\ Sig(DKP(q)[s][2].id) = s
         /\ \A w \in TranExclusive(q) : Sig(w) = s =>
              /\ DeepestKnownDepth(s, w) \in Nat
              /\ DeepestKnownDepth(s, w) <= DKP(q)[s][1]
    BY <1>ihP DEF DeepestKnownCorrectP
  <2>cf. /\ DeepestKnown(q)[s][1] \in Nat
         /\ DeepestKnown(q)[s]
              = <<DeepestKnownDepth(s, DeepestKnown(q)[s][2].id),
                  DeepestKnown(q)[s][2]>>
         /\ DeepestKnown(q)[s][2].id \in TranExclusive(q)
         /\ Sig(DeepestKnown(q)[s][2].id) = s
         /\ \A w \in TranExclusive(q) : Sig(w) = s =>
              /\ DeepestKnownDepth(s, w) \in Nat
              /\ DeepestKnownDepth(s, w) <= DeepestKnown(q)[s][1]
    BY <1>ihC, <2>sC DEF DeepestKnownInvariant
  <2>pfst. DKP(q)[s][1] = DeepestKnownDepth(s, DKP(q)[s][2].id)
    <3>1. <<DeepestKnownDepth(s, DKP(q)[s][2].id), DKP(q)[s][2]>>[1]
            = DeepestKnownDepth(s, DKP(q)[s][2].id)
      OBVIOUS
    <3> QED BY <2>pf, <3>1
  <2>cfst. DeepestKnown(q)[s][1]
             = DeepestKnownDepth(s, DeepestKnown(q)[s][2].id)
    <3>1. <<DeepestKnownDepth(s, DeepestKnown(q)[s][2].id),
            DeepestKnown(q)[s][2]>>[1]
            = DeepestKnownDepth(s, DeepestKnown(q)[s][2].id)
      OBVIOUS
    <3> QED BY <2>cf, <3>1
  <2>le1. DKP(q)[s][1] <= DeepestKnown(q)[s][1]
    <3>1. DeepestKnownDepth(s, DKP(q)[s][2].id) <= DeepestKnown(q)[s][1]
      BY <2>pf, <2>cf
    <3> QED BY <2>pfst, <3>1
  <2>le2. DeepestKnown(q)[s][1] <= DKP(q)[s][1]
    <3>1. DeepestKnownDepth(s, DeepestKnown(q)[s][2].id) <= DKP(q)[s][1]
      BY <2>pf, <2>cf
    <3> QED BY <2>cfst, <3>1
  <2> QED BY <2>le1, <2>le2, <2>pf, <2>cf, SMT
<1>natR. \A q \in pr : \A s : DeepestKnownDepth(s, q) \in Nat
  <2> SUFFICES ASSUME NEW q \in pr, NEW s
      PROVE DeepestKnownDepth(s, q) \in Nat
    OBVIOUS
  <2>a. CASE s \in DOMAIN DeepestKnown(q)
    <3>1. DeepestKnown(q)[s][1] \in Nat
      BY <1>ihC, <2>a DEF DeepestKnownInvariant
    <3> QED BY <3>1, <2>a DEF DeepestKnownDepth
  <2>b. CASE s \notin DOMAIN DeepestKnown(q)
    <3> QED BY <2>b DEF DeepestKnownDepth
  <2> QED BY <2>a, <2>b
<1>scand. \A q \in pr : \A s :
            DeepestKnownSignerCand(s, MemoP(q))
              = <<DeepestKnownDepth(s, q), MemoP(q)>>
  <2> SUFFICES ASSUME NEW q \in pr, NEW s
      PROVE DeepestKnownSignerCand(s, MemoP(q))
              = <<DeepestKnownDepth(s, q), MemoP(q)>>
    OBVIOUS
  <2>a. CASE s \in DOMAIN DKP(q)
    <3>1. s \in DOMAIN DeepestKnown(q)  BY <2>a, <1>ihdomP, <1>ihdomC
    <3>2. DKP(q)[s][1] = DeepestKnown(q)[s][1]  BY <2>a, <1>bridge
    <3> QED BY <2>a, <3>1, <3>2
      DEF DeepestKnownSignerCand, DeepestKnownDepth
  <2>b. CASE s \notin DOMAIN DKP(q)
    <3>1. s \notin DOMAIN DeepestKnown(q)  BY <2>b, <1>ihdomP, <1>ihdomC
    <3> QED BY <2>b, <3>1
      DEF DeepestKnownSignerCand, DeepestKnownDepth
  <2> QED BY <2>a, <2>b
\* ------------------------------------------------------------------- domain
<1>dom0. DOMAIN dka = DeepestKnownSigners(rP)
  BY DEF DeepestKnownAssemble
<1>sigid. {Sig(rc.id) : rc \in rP} = {Sig(q) : q \in pr}
  <2>sub. {Sig(rc.id) : rc \in rP} \subseteq {Sig(q) : q \in pr}
    <3> SUFFICES ASSUME NEW rc \in rP
        PROVE Sig(rc.id) \in {Sig(q) : q \in pr}  OBVIOUS
    <3>1. PICK q \in pr : rc = MemoP(q)  OBVIOUS
    <3> QED BY <3>1, <1>idp
  <2>sup. {Sig(q) : q \in pr} \subseteq {Sig(rc.id) : rc \in rP}
    <3> SUFFICES ASSUME NEW q \in pr
        PROVE Sig(q) \in {Sig(rc.id) : rc \in rP}  OBVIOUS
    <3>1. MemoP(q) \in rP  OBVIOUS
    <3> QED BY <3>1, <1>idp
  <2> QED BY <2>sub, <2>sup
<1>dkdom. UNION {DOMAIN rc.deepestknown : rc \in rP}
            = UNION {SigS(TranExclusive(q)) : q \in pr}
  <2>sub. UNION {DOMAIN rc.deepestknown : rc \in rP}
            \subseteq UNION {SigS(TranExclusive(q)) : q \in pr}
    <3> SUFFICES ASSUME NEW s \in UNION {DOMAIN rc.deepestknown : rc \in rP}
        PROVE s \in UNION {SigS(TranExclusive(q)) : q \in pr}  OBVIOUS
    <3>1. PICK rc \in rP : s \in DOMAIN rc.deepestknown  OBVIOUS
    <3>2. PICK q \in pr : rc = MemoP(q)  BY <3>1
    <3>3. s \in SigS(TranExclusive(q))  BY <3>1, <3>2, <1>ihdomP
    <3> QED BY <3>3
  <2>sup. UNION {SigS(TranExclusive(q)) : q \in pr}
            \subseteq UNION {DOMAIN rc.deepestknown : rc \in rP}
    <3> SUFFICES ASSUME NEW q \in pr, NEW s \in SigS(TranExclusive(q))
        PROVE s \in UNION {DOMAIN rc.deepestknown : rc \in rP}  OBVIOUS
    <3>1. MemoP(q) \in rP  OBVIOUS
    <3>2. s \in DOMAIN DKP(q)  BY <1>ihdomP
    <3> QED BY <3>1, <3>2
  <2> QED BY <2>sub, <2>sup
<1>sigTE. SigS(UU)
            = {Sig(q) : q \in pr}
                \cup UNION {SigS(TranExclusive(q)) : q \in pr}
  <2>sub. SigS(UU)
            \subseteq {Sig(q) : q \in pr}
                        \cup UNION {SigS(TranExclusive(q)) : q \in pr}
    <3> SUFFICES ASSUME NEW s \in SigS(UU)
        PROVE s \in {Sig(q) : q \in pr}
                     \cup UNION {SigS(TranExclusive(q)) : q \in pr}
      OBVIOUS
    <3>w. PICK w \in UU : s = Sig(w)  BY DEF SigS
    <3>p. PICK q \in pr : w \in Tran(q)  BY <3>w
    <3>a. CASE w = q
      <4> QED BY <3>w, <3>p, <3>a
    <3>b. CASE w # q
      <4>1. w \in TranExclusive(q)  BY <3>p, <3>b DEF TranExclusive
      <4>2. s \in SigS(TranExclusive(q))  BY <3>w, <4>1 DEF SigS
      <4> QED BY <3>p, <4>2
    <3> QED BY <3>a, <3>b
  <2>sup. {Sig(q) : q \in pr}
            \cup UNION {SigS(TranExclusive(q)) : q \in pr}
            \subseteq SigS(UU)
    <3>1. \A q \in pr : Sig(q) \in SigS(UU)  BY <1>pTE DEF SigS
    <3>2. \A q \in pr : SigS(TranExclusive(q)) \subseteq SigS(UU)
      BY <1>texPP DEF SigS
    <3> QED BY <3>1, <3>2
  <2> QED BY <2>sub, <2>sup
<1>dom. DOMAIN dka = SigS(UU)
  BY <1>dom0, <1>sigid, <1>dkdom, <1>sigTE DEF DeepestKnownSigners
\* -------------------------------------------------------------------- per-s
<1>main. \A s \in DOMAIN dka :
       /\ dka[s][2] = MemoP(dka[s][2].id)
       /\ dka[s][2].id \in UU
       /\ Sig(dka[s][2].id) = s
       /\ dka[s][1] \in Nat
       /\ dka[s] = <<DeepestKnownDepth(s, dka[s][2].id), dka[s][2]>>
       /\ \A w \in UU : Sig(w) = s =>
            /\ DeepestKnownDepth(s, w) \in Nat
            /\ DeepestKnownDepth(s, w) <= dka[s][1]
  <2> SUFFICES ASSUME NEW s \in DOMAIN dka
      PROVE /\ dka[s][2] = MemoP(dka[s][2].id)
            /\ dka[s][2].id \in UU
            /\ Sig(dka[s][2].id) = s
            /\ dka[s][1] \in Nat
            /\ dka[s] = <<DeepestKnownDepth(s, dka[s][2].id), dka[s][2]>>
            /\ \A w \in UU : Sig(w) = s =>
                 /\ DeepestKnownDepth(s, w) \in Nat
                 /\ DeepestKnownDepth(s, w) <= dka[s][1]
    OBVIOUS
  <2> DEFINE C == DeepestKnownCandidates(s, rP)
  <2>sD. s \in DeepestKnownSigners(rP)  BY <1>dom0
  <2>ent. dka[s]
            = CHOOSE c \in DeepestKnownCandidates(s, rP) :
                \A c2 \in DeepestKnownCandidates(s, rP) : c[1] >= c2[1]
    BY <2>sD DEF DeepestKnownAssemble
  <2>candS. \A q \in pr : Sig(q) = s =>
              DeepestKnownSignerCand(s, MemoP(q)) \in C
    <3> SUFFICES ASSUME NEW q \in pr, Sig(q) = s
        PROVE DeepestKnownSignerCand(s, MemoP(q)) \in C
      OBVIOUS
    <3>1. MemoP(q) \in rP  OBVIOUS
    <3>2. Sig(MemoP(q).id) = s  BY <1>idp
    <3>3. MemoP(q) \in {y \in rP : Sig(y.id) = s}  BY <3>1, <3>2
    <3> QED BY <3>3 DEF DeepestKnownCandidates
  <2>candC. \A q \in pr : (Sig(q) # s /\ s \in DOMAIN DKP(q)) =>
              DKP(q)[s] \in C
    <3> SUFFICES ASSUME NEW q \in pr, Sig(q) # s, s \in DOMAIN DKP(q)
        PROVE DKP(q)[s] \in C
      OBVIOUS
    <3>1. MemoP(q) \in rP  OBVIOUS
    <3>2. Sig(MemoP(q).id) # s  BY <1>idp
    <3>3. MemoP(q)
            \in {y \in rP : Sig(y.id) # s /\ s \in DOMAIN y.deepestknown}
      BY <3>1, <3>2
    <3>4. DeepestKnownCarrierCand(s, MemoP(q)) = DKP(q)[s]
      BY DEF DeepestKnownCarrierCand
    <3> QED BY <3>3, <3>4 DEF DeepestKnownCandidates
  <2>shape. \A c \in C : /\ c[2] = MemoP(c[2].id)
                         /\ c[2].id \in UU
                         /\ Sig(c[2].id) = s
                         /\ c[1] \in Nat
                         /\ c = <<DeepestKnownDepth(s, c[2].id), c[2]>>
    <3> SUFFICES ASSUME NEW c \in C
        PROVE /\ c[2] = MemoP(c[2].id)
              /\ c[2].id \in UU
              /\ Sig(c[2].id) = s
              /\ c[1] \in Nat
              /\ c = <<DeepestKnownDepth(s, c[2].id), c[2]>>
      OBVIOUS
    <3>split.
        \/ c \in {DeepestKnownSignerCand(s, rc) :
                    rc \in {y \in rP : Sig(y.id) = s}}
        \/ c \in {DeepestKnownCarrierCand(s, rc) :
                    rc \in {y \in rP :
                              Sig(y.id) # s /\ s \in DOMAIN y.deepestknown}}
      BY DEF DeepestKnownCandidates
    <3>a. CASE c \in {DeepestKnownSignerCand(s, rc) :
                        rc \in {y \in rP : Sig(y.id) = s}}
      <4>rc. PICK rc \in {y \in rP : Sig(y.id) = s} :
               c = DeepestKnownSignerCand(s, rc)
        BY <3>a
      <4>q. PICK q \in pr : rc = MemoP(q)  BY <4>rc
      <4>sig. Sig(q) = s  BY <4>rc, <4>q, <1>idp
      <4>ceq. c = <<DeepestKnownDepth(s, q), MemoP(q)>>
        BY <4>rc, <4>q, <1>scand
      <4>id. MemoP(q).id = q  BY <1>idp
      <4>nat. DeepestKnownDepth(s, q) \in Nat  BY <1>natR
      <4>tex. q \in UU  BY <1>pTE
      <4> QED BY <4>ceq, <4>id, <4>nat, <4>tex, <4>sig
    <3>b. CASE c \in {DeepestKnownCarrierCand(s, rc) :
                        rc \in {y \in rP :
                                  Sig(y.id) # s
                                  /\ s \in DOMAIN y.deepestknown}}
      <4>rc. PICK rc \in {y \in rP :
                            Sig(y.id) # s /\ s \in DOMAIN y.deepestknown} :
               c = DeepestKnownCarrierCand(s, rc)
        BY <3>b
      <4>q. PICK q \in pr : rc = MemoP(q)  BY <4>rc
      <4>c2. c = DKP(q)[s] /\ s \in DOMAIN DKP(q)
        BY <4>rc, <4>q DEF DeepestKnownCarrierCand
      <4>ihp. DeepestKnownCorrectP(q, DKP(q))  BY <1>ihP
      <4>facts. /\ DKP(q)[s][2] = MemoP(DKP(q)[s][2].id)
                /\ DKP(q)[s][2].id \in TranExclusive(q)
                /\ Sig(DKP(q)[s][2].id) = s
                /\ DKP(q)[s][1] \in Nat
                /\ DKP(q)[s]
                     = <<DeepestKnownDepth(s, DKP(q)[s][2].id),
                         DKP(q)[s][2]>>
        BY <4>ihp, <4>c2 DEF DeepestKnownCorrectP
      <4>tex. DKP(q)[s][2].id \in UU  BY <4>facts, <1>texPP
      <4> QED BY <4>c2, <4>facts, <4>tex
    <3> QED BY <3>split, <3>a, <3>b
  <2>ne. C # {}
    <3>1. \/ s \in {Sig(rc.id) : rc \in rP}
          \/ s \in UNION {DOMAIN rc.deepestknown : rc \in rP}
      BY <2>sD DEF DeepestKnownSigners
    <3>a. CASE s \in {Sig(rc.id) : rc \in rP}
      <4>1. s \in {Sig(q) : q \in pr}  BY <3>a, <1>sigid
      <4>2. PICK q \in pr : s = Sig(q)  BY <4>1
      <4> QED BY <4>2, <2>candS
    <3>b. CASE s \in UNION {DOMAIN rc.deepestknown : rc \in rP}
      <4>1. s \in UNION {SigS(TranExclusive(q)) : q \in pr}
        BY <3>b, <1>dkdom
      <4>2. PICK q \in pr : s \in SigS(TranExclusive(q))  BY <4>1
      <4>3. s \in DOMAIN DKP(q)  BY <4>2, <1>ihdomP
      <4>a. CASE Sig(q) = s
        <5> QED BY <4>a, <2>candS
      <4>b. CASE Sig(q) # s
        <5> QED BY <4>3, <4>b, <2>candC
      <4> QED BY <4>a, <4>b
    <3> QED BY <3>1, <3>a, <3>b
  <2>fin. IsFiniteSet(C)
    <3>frP. IsFiniteSet(rP)  BY FS_Image
    <3>f1. IsFiniteSet({y \in rP : Sig(y.id) = s})  BY <3>frP, FS_Subset
    <3>f2. IsFiniteSet({y \in rP :
                          Sig(y.id) # s /\ s \in DOMAIN y.deepestknown})
      BY <3>frP, FS_Subset
    <3>fS. IsFiniteSet({DeepestKnownSignerCand(s, rc) :
                          rc \in {y \in rP : Sig(y.id) = s}})
      BY <3>f1, FS_Image
    <3>fC. IsFiniteSet({DeepestKnownCarrierCand(s, rc) :
                          rc \in {y \in rP :
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
  <2>c12345. /\ dka[s][2] = MemoP(dka[s][2].id)
             /\ dka[s][2].id \in UU
             /\ Sig(dka[s][2].id) = s
             /\ dka[s][1] \in Nat
             /\ dka[s] = <<DeepestKnownDepth(s, dka[s][2].id), dka[s][2]>>
    BY <2>win, <2>shape
  <2>deep. \A w \in UU : Sig(w) = s =>
             /\ DeepestKnownDepth(s, w) \in Nat
             /\ DeepestKnownDepth(s, w) <= dka[s][1]
    <3> SUFFICES ASSUME NEW w \in UU, Sig(w) = s
        PROVE /\ DeepestKnownDepth(s, w) \in Nat
              /\ DeepestKnownDepth(s, w) <= dka[s][1]
      OBVIOUS
    <3>p. PICK q \in pr : w \in Tran(q)  OBVIOUS
    <3>wtyp. dka[s][1] \in Nat  BY <2>c12345
    <3>a. CASE w = q
      <4>sig. Sig(q) = s  BY <3>a
      <4>c. DeepestKnownSignerCand(s, MemoP(q)) \in C  BY <4>sig, <2>candS
      <4>ceq. DeepestKnownSignerCand(s, MemoP(q))
                = <<DeepestKnownDepth(s, q), MemoP(q)>>
        BY <1>scand
      <4>le. dka[s][1] >= DeepestKnownDepth(s, q)
        <5>1. <<DeepestKnownDepth(s, q), MemoP(q)>>[1]
                = DeepestKnownDepth(s, q)
          OBVIOUS
        <5> QED BY <4>c, <4>ceq, <5>1, <2>win
      <4> QED BY <3>a, <4>le, <1>natR, <3>wtyp
    <3>b. CASE w # q
      <4>wTE. w \in TranExclusive(q)  BY <3>p, <3>b DEF TranExclusive
      <4>ihp. DeepestKnownCorrectP(q, DKP(q))  BY <1>ihP
      <4>sdom. s \in DOMAIN DKP(q)
        <5>1. s \in SigS(TranExclusive(q))  BY <4>wTE DEF SigS
        <5> QED BY <5>1, <1>ihdomP
      <4>bound. /\ DeepestKnownDepth(s, w) \in Nat
                /\ DeepestKnownDepth(s, w) <= DKP(q)[s][1]
        BY <4>ihp, <4>sdom, <4>wTE DEF DeepestKnownCorrectP
      <4>ptyp. DKP(q)[s][1] \in Nat
        BY <4>ihp, <4>sdom DEF DeepestKnownCorrectP
      <4>a. CASE Sig(q) = s
        <5>c. DeepestKnownSignerCand(s, MemoP(q)) \in C  BY <4>a, <2>candS
        <5>ceq. DeepestKnownSignerCand(s, MemoP(q))
                  = <<DeepestKnownDepth(s, q), MemoP(q)>>
          BY <1>scand
        <5>dc. s \in DOMAIN DeepestKnown(q)
          BY <4>sdom, <1>ihdomP, <1>ihdomC
        <5>br. DKP(q)[s][1] = DeepestKnown(q)[s][1]  BY <4>sdom, <1>bridge
        <5>dp. DeepestKnownDepth(s, q) = DKP(q)[s][1] + 1
          BY <5>dc, <5>br DEF DeepestKnownDepth
        <5>le. dka[s][1] >= DeepestKnownDepth(s, q)
          <6>1. <<DeepestKnownDepth(s, q), MemoP(q)>>[1]
                  = DeepestKnownDepth(s, q)
            OBVIOUS
          <6> QED BY <5>c, <5>ceq, <6>1, <2>win
        <5> QED BY <4>bound, <5>dp, <5>le, <4>ptyp, <3>wtyp, SMT
      <4>b. CASE Sig(q) # s
        <5>c. DKP(q)[s] \in C  BY <4>b, <4>sdom, <2>candC
        <5>le. dka[s][1] >= DKP(q)[s][1]  BY <5>c, <2>win
        <5> QED BY <4>bound, <5>le, <4>ptyp, <3>wtyp, SMT
      <4> QED BY <4>a, <4>b
    <3> QED BY <3>a, <3>b
  <2> QED BY <2>c12345, <2>deep
<1> QED BY <1>dom, <1>main DEF DeepestKnownCorrectUP
=============================================================================
