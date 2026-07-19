------------------------- MODULE XFastProof -------------------------
\* Lemma scaffold for AgreementM's FAST case via the MUTUAL-WITNESSING
\* argument.
\*
\* !!! REFUTED (2026-07-16) -- see TLCLaunder.tla + DecisionFastSoundness.md.
\* DecisionFast (amended) is UNSOUND: the "connectivity laundering"
\* counterexample (machine-checked: graph TLAPS-verified in XFastCE3Graph,
\* DAG + violation TLC-verified in TLCLaunder) falsifies AgreementM.  In
\* consequence the following lemmas below are FALSE -- do NOT try to prove
\* them:
\*   WidthUnexcusableStep (OMITTED; known false),
\*   WidthUnexcusable, FreshDescentImpossible, AgreementCaseFast
\*   (all three "proven" only relative to the false OMITTED step; TLCLaunder
\*   witnesses their negations, e.g. BadOneB(20, XRA, 0) holds at ballot
\*   lobal+3 with Fresh TRUE).
\* Still true and machine-verified: A1-A7, FastSqueeze, FreshForcesCarrier,
\* CarrierBelowOneB, WidthUnexcusableBase (the countermodel's ballot-lobal+1
\* 1b dodges BadOneB-hood by seeing no L-good conflict, consistently).
\*
\* EXTENDS the fully-verified MessageInterface; reuses its proven lemmas.

EXTENDS MessageInterface
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE FiniteSetTheorems

\* ===================================================================
\* A1-A7: small, definitely-true building blocks (each reuses 1-2 proven
\* MessageInterface lemmas).  Safe to prove independently.
\* ===================================================================

\* A1. Connectivity survives from the closure into any closure message's view.
\*     (ConFromCaughtSym + CaughtSubClosure + ConFromCaughtAntitone.)
LEMMA ConSurvivesIntoView ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions,
         NEW mset \in SUBSET Messages,
         NEW alpha \in Learners, NEW beta \in Learners,
         beta \in ConFromCaught(alpha, CaughtS(TranClosure(mset))),
         NEW r \in TranClosure(mset)
  PROVE alpha \in Con(beta, r)
<1>mi. TypeOKMessageInterface /\ TranTrans
  BY DEF MessageInterfaceAssumptions
<1>1. beta \in ConFromCaught(alpha, Caught(r))
  <2>sub. Caught(r) \subseteq CaughtS(TranClosure(mset))  BY <1>mi, CaughtSubClosure
  <2> QED BY <2>sub, ConFromCaughtAntitone
<1>2. alpha \in ConFromCaught(beta, Caught(r))  BY <1>1, ConFromCaughtSym
<1> QED BY <1>2 DEF Con

\* A2. A learner connected to beta as of r is self-connected as of r, with an
\*     uncaught {gamma} safety set.  (Condensation: S_{beta,gamma} in SS({gamma}).)
LEMMA GammaSelfConn ==
  ASSUME LearnerGraphAssumptions,
         NEW gamma \in Learners, NEW beta \in Learners, NEW r,
         gamma \in Con(beta, r)
  PROVE \E s \in SafetySets({gamma}) : s \cap Caught(r) = {}
<1>cond. CondensedLearnerGraphAssumption  BY DEF LearnerGraphAssumptions
<1>1. PICK s \in SafetySets({beta, gamma}) : s \cap Caught(r) = {}  BY DEF Con, ConFromCaught
<1>2. SafetySets({gamma, beta}) \subseteq SafetySets({gamma, gamma})  BY <1>cond, AgreementImpliesSelfAgreement
<1>3. {gamma, beta} = {beta, gamma}  OBVIOUS
<1>4. s \in SafetySets({gamma, gamma})  BY <1>1, <1>2, <1>3
<1>5. {gamma, gamma} = {gamma}  OBVIOUS
<1> QED BY <1>1, <1>4, <1>5

\* A3. Transitivity into L: a learner connected to beta as of r, with alpha
\*     also connected to beta as of r and x0 in the fast set below r, lies in
\*     L.  (ConFromCaughtCondensedTrans + antitone Caught(x0) subset Caught(r).)
\*     NB: added r \in Messages -- ConMonotoneTran needs it, and x0 \in Tran(r)
\*     alone does not force it.
LEMMA GammaInL ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions,
         NEW mset \in SUBSET Messages,
         NEW alpha \in Learners, NEW beta \in Learners, NEW gamma \in Learners,
         NEW lobal \in Ballots,
         NEW s \in SUBSET {x \in TranClosure(mset) : B(x) = lobal},
         NEW x0 \in s, NEW r \in Messages, x0 \in Tran(r),
         alpha \in Con(beta, r), gamma \in Con(beta, r)
  PROVE gamma \in ({alpha} \cup UNION {Con(alpha, x) : x \in s})
<1>mi. TypeOKMessageInterface /\ TranTrans  BY DEF MessageInterfaceAssumptions
<1>bIn. beta \in Con(alpha, r)  BY ConFromCaughtSym DEF Con
<1>trans. gamma \in Con(alpha, r)
  <2>cond. CondensedLearnerGraphAssumption  BY DEF LearnerGraphAssumptions
  <2>b. beta \in ConFromCaught(alpha, Caught(r))  BY <1>bIn DEF Con
  <2>g. gamma \in ConFromCaught(beta, Caught(r))  BY DEF Con
  <2>1. gamma \in ConFromCaught(alpha, Caught(r))  BY <2>cond, <2>b, <2>g, ConFromCaughtCondensedTrans
  <2> QED BY <2>1 DEF Con
<1>mono. Con(alpha, r) \subseteq Con(alpha, x0)  BY <1>mi, ConMonotoneTran
<1>final. gamma \in Con(alpha, x0)  BY <1>trans, <1>mono
<1> QED BY <1>final

\* A4. The width below a fast-set element is a Quorums(gamma) for gamma in L.
\*     (cond 2b instantiated at x = x0, l = gamma.)
LEMMA WidthIsGammaQuorum ==
  ASSUME NEW mset, NEW lobal, NEW gamma,
         NEW s, NEW x0 \in s,
         NEW L, gamma \in L,
         \A x \in s : \A l \in L :
           SigS({y \in TranExclusive(x) : B(y) = lobal /\ L \subseteq Lrns(y)}) \in Quorums(l)
  PROVE SigS({y \in TranExclusive(x0) : B(y) = lobal /\ L \subseteq Lrns(y)}) \in Quorums(gamma)
OBVIOUS

\* A5. A message carrying gamma sits atop a Quorums(gamma) of depth-0 witnesses.
\*     (HasDepthDef at d = 1.)
LEMMA ForkIsGammaQuorum ==
  ASSUME MessageInterfaceAssumptions,
         NEW p \in Messages, NEW gamma \in Learners, gamma \in Lrns(p)
  PROVE SigS(Qd(gamma, p, 1)) \in Quorums(gamma)
<1>mi. TypeOKMessageInterface /\ TranTrans /\ TranFinite /\ TranAcyclic
  BY DEF MessageInterfaceAssumptions
<1>hd. HasDepth(gamma, p, 1)  BY DEF Lrns
<1>1nat. 1 \in Nat  OBVIOUS
<1>eq. HasDepth(gamma, p, 1) =
        (/\ Sig(p) \in Acceptors
         /\ IF 1 = 0 THEN (IsOneB(p) /\ Fresh(gamma, p))
                     ELSE SigS(Qd(gamma, p, 1)) \in Quorums(gamma))
  BY <1>mi, <1>1nat, HasDepthDef
<1> QED BY <1>hd, <1>eq

\* A6. Two Quorums(gamma) sharing an uncaught-as-of-r safety set intersect in
\*     an acceptor uncaught as of r.  (SafeQuorumsIntersectUncaught, l1=l2=gamma.)
LEMMA WidthForkShareUncaught ==
  ASSUME ValidLearnerGraphAssumption,
         NEW gamma \in Learners, NEW r,
         NEW W, SigS(W) \in Quorums(gamma),
         NEW Q, SigS(Q) \in Quorums(gamma),
         NEW sfs \in SafetySets({gamma}), sfs \cap Caught(r) = {}
  PROVE \E c \in Acceptors : c \in SigS(W) /\ c \in SigS(Q) /\ c \notin Caught(r)
<1>eq. {gamma, gamma} = {gamma}  OBVIOUS
<1>sfs. sfs \in SafetySets({gamma, gamma})  BY <1>eq
<1> QED BY <1>sfs, SafeQuorumsIntersectUncaught

\* A7. An uncaught-as-of-M acceptor's two M-messages are Tran-ordered by
\*     ballot: a lower-ballot one is in the history of a higher-ballot one.
\*     (UncaughtSameSigComparable + BMonotone.)  Generalized from the
\*     scaffold's Tran(rc)-only framing to an explicit ambient set M -- with
\*     M := Tran(rc), UncaughtSameSigComparable needs wg \in M *already*, so
\*     "Sig(wg) \notin Caught(rc)" alone could never establish wg \in Tran(rc);
\*     callers supply M, e.g. TranClosure(mset).
LEMMA SharedSignerSeesWidth ==
  ASSUME MessageInterfaceAssumptions,
         NEW M, NEW wg \in M, NEW rc \in M, wg \in Messages, rc \in Messages,
         Sig(wg) = Sig(rc), Sig(wg) \in Acceptors, Sig(wg) \notin CaughtS(M),
         B(wg) < B(rc)
  PROVE wg \in Tran(rc)
<1>mi. TypeOKMessageInterface /\ TranTrans /\ TranFinite /\ TranAcyclic /\ AlwaysAProposal
  BY DEF MessageInterfaceAssumptions
<1>cmp. wg \in Tran(rc) \/ rc \in Tran(wg)
  BY UncaughtSameSigComparable
<1>notrev. rc \notin Tran(wg)
  <2> SUFFICES ASSUME rc \in Tran(wg) PROVE FALSE  OBVIOUS
  <2>1. B(rc) <= B(wg)  BY <1>mi, BMonotone
  <2>rcB. B(rc) \in Ballots  BY <1>mi, BBallot
  <2>wgB. B(wg) \in Ballots  BY <1>mi, BBallot
  <2>3. B(rc) \in Nat /\ B(wg) \in Nat  BY <2>rcB, <2>wgB DEF Ballots
  <2> QED BY <2>1, <2>3
<1> QED BY <1>cmp, <1>notrev

\* ===================================================================
\* FastSqueeze: an uncaught acceptor signs both a fast-set message and a fresh
\* high beta-1b, with the former in the latter's history.  (Provable now via
\* SafeQuorumsIntersectUncaught + DecisionHighWitness + UncaughtSameSigComparable.)
\* ===================================================================
LEMMA FastSqueeze ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions, ValueInterfaceAssumptions,
         NEW mset \in SUBSET Messages,
         NEW alpha \in Learners, NEW beta \in Learners,
         NEW lobal \in Ballots, NEW hibal \in Ballots, lobal < hibal,
         NEW s \in SUBSET {x \in TranClosure(mset) : B(x) = lobal},
         SigS(s) \in Quorums(alpha),
         NEW himsg \in TranClosure(mset), B(himsg) = hibal, beta \in Lrns(himsg),
         beta \in ConFromCaught(alpha, CaughtS(TranClosure(mset)))
  PROVE \E x0 \in s : \E rstar \in Qd(beta, himsg, 1) :
          /\ Sig(x0) = Sig(rstar)
          /\ Sig(x0) \notin CaughtS(TranClosure(mset))
          /\ x0 \in Tran(rstar)
<1>mi. TypeOKMessageInterface /\ TranTrans /\ TranFinite /\ TranAcyclic /\ AlwaysAProposal
  BY DEF MessageInterfaceAssumptions
<1>hmMsg. himsg \in Messages  BY <1>mi, TranClosureClosed
<1>hd. HasDepth(beta, himsg, 1)  BY DEF Lrns
<1>1nat. 1 \in Nat  OBVIOUS
<1>eq. HasDepth(beta, himsg, 1) =
        (/\ Sig(himsg) \in Acceptors
         /\ IF 1 = 0 THEN (IsOneB(himsg) /\ Fresh(beta, himsg))
                     ELSE SigS(Qd(beta, himsg, 1)) \in Quorums(beta))
  BY <1>mi, <1>hmMsg, <1>1nat, HasDepthDef
<1>quo2. SigS(Qd(beta, himsg, 1)) \in Quorums(beta)  BY <1>hd, <1>eq
<1>sfs. PICK sfs \in SafetySets({alpha, beta}) : sfs \cap CaughtS(TranClosure(mset)) = {}
  BY DEF ConFromCaught
<1>vlga. ValidLearnerGraphAssumption  BY DEF LearnerGraphAssumptions
<1>squeeze. PICK a \in Acceptors :
              /\ a \in SigS(s) /\ a \in SigS(Qd(beta, himsg, 1))
              /\ a \notin CaughtS(TranClosure(mset))
  BY <1>vlga, <1>sfs, <1>quo2, SafeQuorumsIntersectUncaught
<1>x0. PICK x0 \in s : a = Sig(x0)  BY <1>squeeze DEF SigS
<1>rstar. PICK rstar \in Qd(beta, himsg, 1) : a = Sig(rstar)  BY <1>squeeze DEF SigS
<1>sigeq. Sig(x0) = Sig(rstar)  BY <1>x0, <1>rstar
<1>uncaught. Sig(x0) \notin CaughtS(TranClosure(mset))  BY <1>squeeze, <1>x0
<1>x0lobal. B(x0) = lobal  OBVIOUS
<1>x0TC. x0 \in TranClosure(mset)  OBVIOUS
<1>rstarDef. rstar \in TranExclusive(himsg) /\ B(himsg) = B(rstar) /\ HasDepth(beta, rstar, 0)
  BY <1>rstar DEF Qd
<1>rstarHi. B(rstar) = hibal  BY <1>rstarDef
<1>rstarTran. rstar \in Tran(himsg)  BY <1>rstarDef DEF TranExclusive
<1>rstarTC. rstar \in TranClosure(mset)
  <2>1. Tran(himsg) \subseteq TranClosure(mset)  BY <1>mi, TranClosureClosed
  <2> QED BY <2>1, <1>rstarTran
<1>x0inA. Sig(x0) \in Acceptors  BY <1>x0, <1>squeeze
<1>blt. B(x0) < B(rstar)  BY <1>x0lobal, <1>rstarHi
<1>x0Msg. x0 \in Messages  BY <1>mi, <1>x0TC, TranClosureClosed
<1>rstarMsg. rstar \in Messages  BY <1>mi, <1>rstarTC, TranClosureClosed
<1>final. x0 \in Tran(rstar)
  BY <1>mi, <1>x0TC, <1>rstarTC, <1>x0Msg, <1>rstarMsg, <1>sigeq, <1>x0inA, <1>uncaught, <1>blt,
     SharedSignerSeesWidth
<1> QED BY <1>x0, <1>rstar, <1>sigeq, <1>uncaught, <1>final

\* ===================================================================
\* FreshForcesCarrier: a fresh beta-1b that sees a value-differing message
\* carrying a connected learner is forced (FreshTopConnected) to also see a
\* MAXIMAL such carrier whose value equals the 1b's.  (Direct FreshTopConnected.)
\* ===================================================================
LEMMA FreshForcesCarrier ==
  ASSUME MessageInterfaceAssumptions,
         NEW gamma \in Learners, NEW r \in Messages, Fresh(gamma, r),
         NEW w \in Tran(r), V(w) # V(r), Con(gamma, r) \cap Lrns(w) # {}
  PROVE \E p \in Tran(r) :
          /\ B(p) > B(w) /\ V(p) = V(r) /\ Con(gamma, r) \cap Lrns(p) # {}
<1>mi. TypeOKMessageInterface /\ TranTrans /\ TranFinite /\ TranAcyclic /\ AlwaysAProposal
  BY DEF MessageInterfaceAssumptions
<1> QED BY <1>mi, FreshTopConnected

\* ===================================================================
\* THE CRUX, decomposed as a BALLOT INDUCTION.  The whole soundness question
\* now reduces to ONE lemma: WidthUnexcusableStep.  Everything else here is
\* clean.
\* ===================================================================

\* A8. A learner-carrying message in a OneB m's strict history is at a
\*     STRICTLY lower ballot -- else it (or a witness one level below it, via
\*     HasDepth(l,p,1)'s Qd(l,p,1) member) is a 3rd distinct message at
\*     B(m), breaking IsOneB (Cardinality({x in Tran(m): B(x)=B(m)})=2).  This
\*     is the engine of the ballot descent.  NB: added LearnerGraphAssumptions
\*     -- QuorumsHaveMembers (to get a concrete witness out of the Qd(l,p,1)
\*     quorum) needs it.
LEMMA CarrierBelowOneB ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions,
         NEW m \in Messages, IsOneB(m),
         NEW p \in TranExclusive(m), NEW l \in Learners, l \in Lrns(p)
  PROVE B(p) < B(m)
<1>mi. TypeOKMessageInterface /\ TranTrans /\ TranFinite /\ TranAcyclic /\ AlwaysAProposal
  BY DEF MessageInterfaceAssumptions
<1>pTranM. p \in Tran(m) /\ p # m  BY DEF TranExclusive
<1>mSubM. Tran(m) \subseteq Messages  BY <1>mi, TranSubMessages
<1>pM. p \in Messages  BY <1>pTranM, <1>mSubM
<1>le. B(p) <= B(m)  BY <1>mi, <1>pTranM, BMonotone
<1>ne. B(p) # B(m)
  <2> SUFFICES ASSUME B(p) = B(m) PROVE FALSE  OBVIOUS
  <2>hd. HasDepth(l, p, 1)  BY DEF Lrns
  <2>1nat. 1 \in Nat  OBVIOUS
  <2>eq. HasDepth(l, p, 1) =
          (/\ Sig(p) \in Acceptors
           /\ IF 1 = 0 THEN (IsOneB(p) /\ Fresh(l, p))
                       ELSE SigS(Qd(l, p, 1)) \in Quorums(l))
    BY <1>mi, <1>pM, <2>1nat, HasDepthDef
  <2>quo. SigS(Qd(l, p, 1)) \in Quorums(l)  BY <2>hd, <2>eq
  <2>lga. LearnersMightAgree /\ ValidLearnerGraphAssumption  BY DEF LearnerGraphAssumptions
  <2>sne. SigS(Qd(l, p, 1)) # {}  BY <2>lga, <2>quo, QuorumsHaveMembers
  <2>qdne. Qd(l, p, 1) # {}  BY <2>sne DEF SigS
  <2> PICK x \in Qd(l, p, 1) : TRUE  BY <2>qdne
  <2>xdef. x \in TranExclusive(p) /\ B(p) = B(x) /\ HasDepth(l, x, 0)  BY DEF Qd
  <2>xp. x \in Tran(p) /\ x # p  BY <2>xdef DEF TranExclusive
  <2>subpm. Tran(p) \subseteq Tran(m)  BY <1>mi, <1>pTranM DEF TranTrans
  <2>xM. x \in Tran(m)  BY <2>xp, <2>subpm
  <2>xnem. x # m
    <3> SUFFICES ASSUME x = m PROVE FALSE  OBVIOUS
    <3>1. m \in Tran(p)  BY <2>xp
    <3>2. p = m  BY <3>1, <1>pTranM, <1>pM, <1>mi, TranAntisym
    <3> QED BY <3>2, <1>pTranM
  <2>Bx. B(x) = B(m)  BY <2>xdef
  <2>c1. IsFiniteSet({m}) /\ Cardinality({m}) = 1  BY FS_Singleton
  <2>add1. IsFiniteSet({m} \cup {p}) /\
           Cardinality({m} \cup {p}) = IF p \in {m} THEN Cardinality({m}) ELSE Cardinality({m})+1
    BY <2>c1, FS_AddElement
  <2>pnotm. p \notin {m}  BY <1>pTranM
  <2>c2. IsFiniteSet({m,p}) /\ Cardinality({m,p}) = 2  BY <2>add1, <2>pnotm, <2>c1
  <2>add2. IsFiniteSet({m,p} \cup {x}) /\
           Cardinality({m,p} \cup {x}) = IF x \in {m,p} THEN Cardinality({m,p}) ELSE Cardinality({m,p})+1
    BY <2>c2, FS_AddElement
  <2>xnotmp. x \notin {m,p}  BY <2>xnem, <2>xp
  <2>c3. IsFiniteSet({m,p,x}) /\ Cardinality({m,p,x}) = 3  BY <2>add2, <2>xnotmp, <2>c2
  <2>finTranM. IsFiniteSet(Tran(m))  BY <1>mi DEF TranFinite
  <2>finTgt. IsFiniteSet({y \in Tran(m) : B(y) = B(m)})  BY <2>finTranM, FS_Subset
  <2>subS. {m,p,x} \subseteq {y \in Tran(m) : B(y) = B(m)}
    <3>m. m \in Tran(m) /\ B(m) = B(m)  BY DEF Tran
    <3>p. p \in Tran(m) /\ B(p) = B(m)  BY <1>pTranM
    <3>x. x \in Tran(m) /\ B(x) = B(m)  BY <2>xM, <2>Bx
    <3> QED BY <3>m, <3>p, <3>x
  <2>subcard. Cardinality({m,p,x}) <= Cardinality({y \in Tran(m) : B(y) = B(m)})
    BY <2>c3, <2>finTgt, <2>subS, FS_Subset
  <2>card2. Cardinality({y \in Tran(m) : B(y) = B(m)}) = 2  BY DEF IsOneB
  <2> QED BY <2>c3, <2>subcard, <2>card2
<1>leNat. B(p) \in Nat /\ B(m) \in Nat
  <2>bp. B(p) \in Ballots  BY <1>mi, <1>pM, BBallot
  <2>bm. B(m) \in Ballots  BY <1>mi, BBallot
  <2> QED BY <2>bp, <2>bm DEF Ballots
<1> QED BY <1>le, <1>ne, <1>leNat

\* The descent invariant: a fresh OneB whose history holds a value-differing
\* ballot-lobal message carrying a learner it is self-connected to.
BadOneB(gamma, m, lobal) ==
  /\ IsOneB(m) /\ Fresh(gamma, m) /\ lobal < B(m)
  /\ gamma \in Con(gamma, m)
  /\ \E wg \in Tran(m) : B(wg) = lobal /\ V(wg) # V(m) /\ gamma \in Lrns(wg)

\* BASE (clean): at ballot lobal+1 no BadOneB exists -- excusing the conflict
\* needs a carrier in the empty ballot interval (lobal, lobal+1).
\* (Fresh disjunct 3 + CarrierBelowOneB + arithmetic.)
LEMMA WidthUnexcusableBase ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions,
         NEW lobal \in Ballots, NEW gamma \in Learners, NEW m \in Messages,
         B(m) = lobal + 1
  PROVE ~BadOneB(gamma, m, lobal)
<1> SUFFICES ASSUME BadOneB(gamma, m, lobal) PROVE FALSE  OBVIOUS
<1>mi. TypeOKMessageInterface /\ TranTrans /\ TranFinite /\ TranAcyclic /\ AlwaysAProposal
  BY DEF MessageInterfaceAssumptions
<1>bad. /\ IsOneB(m) /\ Fresh(gamma, m) /\ lobal < B(m) /\ gamma \in Con(gamma, m)
        /\ \E wg \in Tran(m) : B(wg) = lobal /\ V(wg) # V(m) /\ gamma \in Lrns(wg)
  BY DEF BadOneB
<1>iso. IsOneB(m)  BY <1>bad
<1>fresh. Fresh(gamma, m)  BY <1>bad
<1>gcon. gamma \in Con(gamma, m)  BY <1>bad
<1> PICK wg \in Tran(m) : B(wg) = lobal /\ V(wg) # V(m) /\ gamma \in Lrns(wg)  BY <1>bad
<1>wgIn. B(wg) = lobal /\ V(wg) # V(m) /\ gamma \in Lrns(wg)  OBVIOUS
<1>wginter. Con(gamma, m) \cap Lrns(wg) # {}  BY <1>gcon, <1>wgIn
<1>freshdef. \A x \in Tran(m):
    \/ V(x) = V(m)
    \/ Con(gamma, m) \cap Lrns(x) = {}
    \/ \E p \in TranExclusive(m): B(p) > B(x) /\ Con(gamma, m) \cap Lrns(p) # {}
  BY <1>fresh DEF Fresh
<1>wgTran. wg \in Tran(m)  OBVIOUS
<1>disj. \/ V(wg) = V(m) \/ Con(gamma,m) \cap Lrns(wg) = {}
         \/ \E p \in TranExclusive(m): B(p) > B(wg) /\ Con(gamma,m) \cap Lrns(p) # {}
  BY <1>freshdef, <1>wgTran
<1>third. \E p \in TranExclusive(m): B(p) > B(wg) /\ Con(gamma,m) \cap Lrns(p) # {}
  BY <1>disj, <1>wgIn, <1>wginter
<1> PICK p \in TranExclusive(m) : B(p) > B(wg) /\ Con(gamma, m) \cap Lrns(p) # {}  BY <1>third
<1> PICK l \in Con(gamma, m) \cap Lrns(p) : TRUE  BY <1>third
<1>lLearners. l \in Learners  BY DEF Con, ConFromCaught
<1>llrns. l \in Lrns(p)  OBVIOUS
<1>cbo. B(p) < B(m)  BY <1>mi, <1>iso, <1>lLearners, <1>llrns, CarrierBelowOneB
<1>pgt. B(p) > B(wg)  OBVIOUS
<1>pNat. B(p) \in Nat
  <2>pM. p \in Messages  BY <1>mi, TranSubMessages DEF TranExclusive
  <2>bp. B(p) \in Ballots  BY <1>mi, <2>pM, BBallot
  <2> QED BY <2>bp DEF Ballots
<1>lobalNat. lobal \in Nat  BY DEF Ballots
<1> QED BY <1>cbo, <1>pgt, <1>wgIn, <1>pNat, <1>lobalNat

\* !!! THE ONE OPEN OBLIGATION -- soundness reduces to THIS !!!
\* STEP: given the IH for all lower ballots, no BadOneB at ballot b.  The
\* excusing carrier p is at ballot < b (CarrierBelowOneB), carries gamma_p,
\* and its fresh-1b rc (ballot < b) is fresh.  To apply the IH to rc we must
\* show rc is ITSELF a BadOneB -- i.e. rc SEES a value-differing ballot-lobal
\* message carrying a self-connected learner.  At the TOP that came from
\* intersecting the value-v WIDTH QUORUM against Qd(gamma_p,p,1) (A4-A7); but
\* the width quorum is NOT below rc, and the single shared message it yields
\* is only depth-1 (no width of its own), so the quorum does NOT descend.
\* Whether "sees a conflict" propagates to rc is UNSETTLED and may be
\* MaxDepth-bounded (deep TLC tested only small N).  Crack or refute THIS.
LEMMA WidthUnexcusableStep ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions, ValueInterfaceAssumptions,
         NEW mset \in SUBSET Messages, NEW lobal \in Ballots, NEW b \in Ballots,
         lobal + 1 < b,
         \A gp \in Learners : \A mp \in TranClosure(mset) :
            B(mp) < b => ~BadOneB(gp, mp, lobal),
         NEW gamma \in Learners, NEW m \in TranClosure(mset), B(m) = b
  PROVE ~BadOneB(gamma, m, lobal)
OMITTED

\* The ballot induction: WidthUnexcusableBase + WidthUnexcusableStep by strong
\* induction on B(m).  (GeneralNatInduction on the ballot.)
LEMMA WidthUnexcusable ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions, ValueInterfaceAssumptions,
         NEW mset \in SUBSET Messages, NEW lobal \in Ballots,
         NEW gamma \in Learners, NEW m \in TranClosure(mset)
  PROVE ~BadOneB(gamma, m, lobal)
<1>mi. TypeOKMessageInterface /\ TranTrans /\ TranFinite /\ TranAcyclic /\ AlwaysAProposal
  BY DEF MessageInterfaceAssumptions
<1>lobalNat. lobal \in Nat  BY DEF Ballots
<1> DEFINE Q(b) == \A gp \in Learners : \A mp \in TranClosure(mset) : B(mp) = b => ~BadOneB(gp, mp, lobal)
<1> SUFFICES \A b \in Nat : Q(b)
  <2>mMsg. m \in Messages  BY <1>mi, TranClosureClosed
  <2>bm. B(m) \in Ballots  BY <1>mi, <2>mMsg, BBallot
  <2>bmnat. B(m) \in Nat  BY <2>bm DEF Ballots
  <2>1. Q(B(m))  BY <2>bmnat
  <2> QED BY <2>1 DEF Q
<1> HIDE DEF Q
<1>ind. \A b \in Nat : (\A k \in 0..(b-1) : Q(k)) => Q(b)
  <2> USE DEF Q
  <2> SUFFICES ASSUME NEW b \in Nat, \A k \in 0..(b-1) : Q(k),
                      NEW gp \in Learners, NEW mp \in TranClosure(mset), B(mp) = b
               PROVE ~BadOneB(gp, mp, lobal)
    OBVIOUS
  <2>mpMsg. mp \in Messages  BY <1>mi, TranClosureClosed
  <2>mpBnat. B(mp) \in Nat
    <3>1. B(mp) \in Ballots  BY <1>mi, <2>mpMsg, BBallot
    <3> QED BY <3>1 DEF Ballots
  <2>a. CASE b <= lobal
    <3> SUFFICES ASSUME BadOneB(gp, mp, lobal) PROVE FALSE  OBVIOUS
    <3>1. lobal < B(mp)  BY DEF BadOneB
    <3> QED BY <3>1, <2>a, <1>lobalNat, <2>mpBnat
  <2>b. CASE b = lobal + 1
    <3> QED BY <2>b, <2>mpMsg, WidthUnexcusableBase
  <2>c. CASE b > lobal + 1
    <3>ih. \A gp2 \in Learners : \A mp2 \in TranClosure(mset) : B(mp2) < b => ~BadOneB(gp2, mp2, lobal)
      <4> SUFFICES ASSUME NEW gp2 \in Learners, NEW mp2 \in TranClosure(mset), B(mp2) < b
                   PROVE ~BadOneB(gp2, mp2, lobal)
        OBVIOUS
      <4>mp2Msg. mp2 \in Messages  BY <1>mi, TranClosureClosed
      <4>bmp2nat. B(mp2) \in Nat
        <5>1. B(mp2) \in Ballots  BY <1>mi, <4>mp2Msg, BBallot
        <5> QED BY <5>1 DEF Ballots
      <4>k. B(mp2) \in 0..(b-1)  BY <4>bmp2nat
      <4>qk. Q(B(mp2))  BY <4>k
      <4> QED BY <4>qk
    <3>bBallots. b \in Ballots  BY DEF Ballots
    <3>lt. lobal + 1 < b  BY <2>c
    <3> QED BY <3>bBallots, <3>lt, <3>ih, WidthUnexcusableStep
  <2> QED BY <2>a, <2>b, <2>c, <2>mpBnat, <1>lobalNat
<1> QED BY <1>ind, GeneralNatInduction, IsaM("blast")

\* FreshDescentImpossible now follows from WidthUnexcusable: rstar is a
\* BadOneB (IsOneB, Fresh assumed, lobal<hibal=B(rstar), beta self-connected
\* as of rstar via A1+ConFromCaughtSym+A2, and x0 is the value-differing
\* ballot-lobal witness with beta in L subset Lrns(x0)).  Contradiction.
\* NB: the ASSUME clause spells out L's set expression literally instead of
\* binding it via LET -- a LET-bound hypothesis inside a LEMMA's ASSUME
\* clause silently defeats Zenon/SMT's ability to match/apply the lemma from
\* a BY-citation (confirmed empirically: identical hypotheses supplied
\* without a LET wrapper apply instantly; wrapped in LET, both backends
\* exhaust their search with no diagnostic beyond "Could not prove or check").
LEMMA FreshDescentImpossible ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions, ValueInterfaceAssumptions,
         NEW mset \in SUBSET Messages,
         NEW alpha \in Learners, NEW beta \in Learners,
         NEW lobal \in Ballots, NEW hibal \in Ballots, lobal < hibal,
         BalToVal(lobal) # BalToVal(hibal),
         NEW s \in SUBSET {x \in TranClosure(mset) : B(x) = lobal},
         \A x \in s : ({alpha} \cup UNION {Con(alpha, y) : y \in s}) \subseteq Lrns(x),
         \A x \in s : \A l \in ({alpha} \cup UNION {Con(alpha, y) : y \in s}) :
              SigS({z \in TranExclusive(x) :
                    B(z) = lobal /\ ({alpha} \cup UNION {Con(alpha, y) : y \in s}) \subseteq Lrns(z)}) \in Quorums(l),
         beta \in ConFromCaught(alpha, CaughtS(TranClosure(mset))),
         NEW x0 \in s, NEW rstar \in TranClosure(mset),
         x0 \in Tran(rstar), B(rstar) = hibal, IsOneB(rstar)
  PROVE ~Fresh(beta, rstar)
<1>mi. TypeOKMessageInterface /\ TranTrans /\ TranFinite /\ TranAcyclic /\ AlwaysAProposal
  BY DEF MessageInterfaceAssumptions
<1> DEFINE L == {alpha} \cup UNION {Con(alpha, y) : y \in s}
<1>Lx. \A x \in s : L \subseteq Lrns(x)  OBVIOUS
<1>rstarMsg. rstar \in Messages  BY <1>mi, TranClosureClosed
<1>a1. alpha \in Con(beta, rstar)  BY <1>mi, ConSurvivesIntoView
<1>selfconn. beta \in Con(beta, rstar)
  <2>sym. beta \in Con(alpha, rstar)  BY <1>a1, ConFromCaughtSym DEF Con
  <2>a2. \E sfs \in SafetySets({beta}) : sfs \cap Caught(rstar) = {}  BY <2>sym, GammaSelfConn
  <2> PICK sfs \in SafetySets({beta}) : sfs \cap Caught(rstar) = {}  BY <2>a2
  <2>eq. {beta,beta} = {beta}  OBVIOUS
  <2>sfs2. sfs \in SafetySets({beta,beta})  BY <2>eq
  <2> QED BY <2>sfs2 DEF Con, ConFromCaught
<1>xInL. beta \in L  BY <1>mi, <1>a1, <1>selfconn, <1>rstarMsg, GammaInL
<1>wgLrns. beta \in Lrns(x0)  BY <1>Lx, <1>xInL
<1>x0lobal. B(x0) = lobal  OBVIOUS
<1>Vdiff. V(x0) # V(rstar)
  <2>1. V(x0) = BalToVal(B(x0))  BY DEF V
  <2>2. V(rstar) = BalToVal(B(rstar))  BY DEF V
  <2> QED BY <2>1, <2>2, <1>x0lobal
<1> SUFFICES ASSUME Fresh(beta, rstar) PROVE FALSE  OBVIOUS
<1>badoneb. BadOneB(beta, rstar, lobal)
  <2>1. lobal < B(rstar)  OBVIOUS
  <2>2. x0 \in Tran(rstar) /\ B(x0) = lobal /\ V(x0) # V(rstar) /\ beta \in Lrns(x0)
    BY <1>x0lobal, <1>Vdiff, <1>wgLrns
  <2>3. \E wg \in Tran(rstar) : B(wg) = lobal /\ V(wg) # V(rstar) /\ beta \in Lrns(wg)
    BY <2>2
  <2> QED BY <2>1, <2>3, <1>selfconn DEF BadOneB
<1>contra. ~BadOneB(beta, rstar, lobal)  BY <1>mi, WidthUnexcusable
<1> QED BY <1>badoneb, <1>contra

\* ===================================================================
\* AgreementCaseFast: the fast branch of AgreementM.  (Assembles the fast-cert
\* unpacking + DecisionHighWitness + FastSqueeze + QdOneBFresh + FreshDescent-
\* Impossible.)  Once proved, AgreementCaseLt's fast branch cites this instead
\* of TraceExistenceFast, and AgreementM follows unchanged.
\* ===================================================================
LEMMA AgreementCaseFast ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions, ValueInterfaceAssumptions,
         NEW mset \in SUBSET Messages,
         NEW alpha \in Learners, NEW beta \in Learners,
         NEW lobal \in Ballots, NEW hibal \in Ballots, lobal < hibal,
         DecisionFast(mset, alpha, lobal),
         Decision(mset, beta, hibal),
         beta \in ConFromCaught(alpha, CaughtS(TranClosure(mset)))
  PROVE BalToVal(lobal) = BalToVal(hibal)
<1>mi. TypeOKMessageInterface /\ TranTrans /\ TranFinite /\ TranAcyclic /\ AlwaysAProposal
  BY DEF MessageInterfaceAssumptions
<1> SUFFICES ASSUME BalToVal(lobal) # BalToVal(hibal) PROVE FALSE  OBVIOUS
<1>df. PICK s \in SUBSET {x \in TranClosure(mset) : B(x) = lobal} :
        LET L == ({alpha} \cup UNION {Con(alpha, x) : x \in s})
         IN /\ \A l \in L : SigS(s) \in Quorums(l)
            /\ \A x \in s :
              /\ L \subseteq Lrns(x)
              /\ \A l \in L :
                 SigS({y \in TranExclusive(x) : B(y) = lobal /\ L \subseteq Lrns(y)}) \in Quorums(l)
  BY DEF DecisionFast
<1> DEFINE L == ({alpha} \cup UNION {Con(alpha, x) : x \in s})
<1>Lall. /\ \A l \in L : SigS(s) \in Quorums(l)
         /\ \A x \in s : /\ L \subseteq Lrns(x)
                         /\ \A l \in L : SigS({y \in TranExclusive(x) : B(y) = lobal /\ L \subseteq Lrns(y)}) \in Quorums(l)
  BY <1>df
<1>LxDist. \A x \in s : ({alpha} \cup UNION {Con(alpha, y) : y \in s}) \subseteq Lrns(x)
  BY <1>Lall DEF L
<1>LqDist. \A x \in s : \A l \in ({alpha} \cup UNION {Con(alpha, y) : y \in s}) :
             SigS({z \in TranExclusive(x) :
                   B(z) = lobal /\ ({alpha} \cup UNION {Con(alpha, y) : y \in s}) \subseteq Lrns(z)}) \in Quorums(l)
  BY <1>Lall DEF L
<1>alphaInL. alpha \in L  OBVIOUS
<1>sQuo. SigS(s) \in Quorums(alpha)  BY <1>Lall, <1>alphaInL
<1>hw. PICK himsg \in TranClosure(mset) : B(himsg) = hibal /\ beta \in Lrns(himsg)
  BY DecisionHighWitness
<1>himsgMsg. himsg \in Messages  BY <1>mi, TranClosureClosed
<1>fsqE. \E x0 \in s : \E rstar \in Qd(beta, himsg, 1) :
           /\ Sig(x0) = Sig(rstar)
           /\ Sig(x0) \notin CaughtS(TranClosure(mset))
           /\ x0 \in Tran(rstar)
  BY <1>sQuo, <1>hw, FastSqueeze
<1>px0. PICK x0 \in s : \E rstar \in Qd(beta, himsg, 1) :
          /\ Sig(x0) = Sig(rstar)
          /\ Sig(x0) \notin CaughtS(TranClosure(mset))
          /\ x0 \in Tran(rstar)
  BY <1>fsqE
<1>prstar. PICK rstar \in Qd(beta, himsg, 1) :
          /\ Sig(x0) = Sig(rstar)
          /\ Sig(x0) \notin CaughtS(TranClosure(mset))
          /\ x0 \in Tran(rstar)
  BY <1>px0
<1>x0Tran. x0 \in Tran(rstar)  BY <1>prstar
<1>qof. IsOneB(rstar) /\ Fresh(beta, rstar) /\ Sig(rstar) \in Acceptors
  BY <1>mi, <1>himsgMsg, <1>prstar, QdOneBFresh
<1>rstarBal. B(rstar) = hibal
  <2>1. rstar \in TranExclusive(himsg) /\ B(himsg) = B(rstar) /\ HasDepth(beta, rstar, 0)  BY <1>prstar DEF Qd
  <2> QED BY <2>1, <1>hw
<1>rstarTC. rstar \in TranClosure(mset)
  <2>1. rstar \in TranExclusive(himsg) /\ B(himsg) = B(rstar) /\ HasDepth(beta, rstar, 0)  BY <1>prstar DEF Qd
  <2>2. rstar \in Tran(himsg)  BY <2>1 DEF TranExclusive
  <2>3. Tran(himsg) \subseteq TranClosure(mset)  BY <1>mi, TranClosureClosed
  <2> QED BY <2>2, <2>3
\* NB: citing FreshDescentImpossible as a single BY-fact here consistently
\* defeats Zenon/SMT/Isabelle-auto (confirmed empirically across many hint
\* phrasings) -- likely a resource limit from correlating its 8 NEW-bound
\* variables plus several triply-nested-quantifier hypotheses in one shot.
\* Its OWN proof steps (which are individually reliable, as proven by
\* FreshDescentImpossible verifying cleanly standalone) are inlined here
\* instead, with AgreementCaseFast's already-established facts feeding in
\* directly.  NB2: the GammaInL/WidthUnexcusable citations below (also
\* individually reliable standalone) additionally needed to stay at the
\* SAME shallow <1>-nesting depth as the rest of this proof, not nested one
\* level deeper inside <1>fdi's own SUFFICES block -- nested one level in,
\* both citations failed (and a HIDE-based attempt to shrink the ambient
\* context at that depth hit an unrelated tlapm internal crash,
\* "proof.Gen.set_expr: This expression does not appear in the context and
\* cannot be hidden"); computing them here as plain <1>-level facts (neither
\* actually depends on the Fresh(beta,rstar) hypothesis <1>fdi assumes for
\* contradiction, so hoisting is sound) resolved it.
<1>isOneB. IsOneB(rstar)  BY <1>qof
<1>rstarMsg. rstar \in Messages  BY <1>mi, <1>rstarTC, TranClosureClosed
<1>a1. alpha \in Con(beta, rstar)  BY <1>mi, <1>rstarTC, ConSurvivesIntoView
<1>selfconn. beta \in Con(beta, rstar)
  <2>sym. beta \in Con(alpha, rstar)  BY <1>a1, ConFromCaughtSym DEF Con
  <2>a2. \E sfs \in SafetySets({beta}) : sfs \cap Caught(rstar) = {}  BY <2>sym, GammaSelfConn
  <2> PICK sfs \in SafetySets({beta}) : sfs \cap Caught(rstar) = {}  BY <2>a2
  <2>eq. {beta,beta} = {beta}  OBVIOUS
  <2>sfs2. sfs \in SafetySets({beta,beta})  BY <2>eq
  <2> QED BY <2>sfs2 DEF Con, ConFromCaught
\* Inlined GammaInL (A3) at gamma:=beta -- also individually reliable
\* standalone, also hit "Zenon error: could not find a proof within the
\* memory size limit" when cited as a single BY-fact here.
<1>xInL. beta \in L
  <2>bIn. beta \in Con(alpha, rstar)  BY <1>a1, ConFromCaughtSym DEF Con
  <2>mono. Con(alpha, rstar) \subseteq Con(alpha, x0)  BY <1>mi, <1>rstarMsg, <1>x0Tran, ConMonotoneTran
  <2>final. beta \in Con(alpha, x0)  BY <2>bIn, <2>mono
  <2> QED BY <2>final
<1>Lx. \A x \in s : L \subseteq Lrns(x)  BY <1>Lall
<1>wgLrns. beta \in Lrns(x0)  BY <1>Lx, <1>xInL
<1>x0lobal. B(x0) = lobal  OBVIOUS
<1>Vdiff. V(x0) # V(rstar)
  <2>1. V(x0) = BalToVal(B(x0))  BY DEF V
  <2>2. V(rstar) = BalToVal(B(rstar))  BY DEF V
  <2> QED BY <2>1, <2>2, <1>x0lobal, <1>rstarBal
\* Inlined WidthUnexcusable (also individually reliable standalone, also
\* fails to apply as a single BY-fact here for the same reason as
\* GammaInL/FreshDescentImpossible above -- "Zenon error: could not find a
\* proof within the memory size limit", and SMT gave no better result).
<1>contra. ~BadOneB(beta, rstar, lobal)
  <2> DEFINE Q(b) == \A gp \in Learners : \A mp \in TranClosure(mset) : B(mp) = b => ~BadOneB(gp, mp, lobal)
  <2> SUFFICES \A b \in Nat : Q(b)
    <3>bm. B(rstar) \in Ballots  BY <1>mi, <1>rstarMsg, BBallot
    <3>bmnat. B(rstar) \in Nat  BY <3>bm DEF Ballots
    <3>1. Q(B(rstar))  BY <3>bmnat
    <3> QED BY <3>1, <1>rstarTC DEF Q
  <2> HIDE DEF Q
  <2>ind. \A b \in Nat : (\A k \in 0..(b-1) : Q(k)) => Q(b)
    <3> USE DEF Q
    <3> SUFFICES ASSUME NEW b \in Nat, \A k \in 0..(b-1) : Q(k),
                        NEW gp \in Learners, NEW mp \in TranClosure(mset), B(mp) = b
                 PROVE ~BadOneB(gp, mp, lobal)
      OBVIOUS
    <3>mpMsg. mp \in Messages  BY <1>mi, TranClosureClosed
    <3>mpBnat. B(mp) \in Nat
      <4>1. B(mp) \in Ballots  BY <1>mi, <3>mpMsg, BBallot
      <4> QED BY <4>1 DEF Ballots
    <3>lobalNat. lobal \in Nat  BY DEF Ballots
    <3>a. CASE b <= lobal
      <4> SUFFICES ASSUME BadOneB(gp, mp, lobal) PROVE FALSE  OBVIOUS
      <4>1. lobal < B(mp)  BY DEF BadOneB
      <4> QED BY <4>1, <3>a, <3>lobalNat, <3>mpBnat
    <3>b. CASE b = lobal + 1
      <4> QED BY <3>b, <3>mpMsg, WidthUnexcusableBase
    <3>c. CASE b > lobal + 1
      <4>ih. \A gp2 \in Learners : \A mp2 \in TranClosure(mset) : B(mp2) < b => ~BadOneB(gp2, mp2, lobal)
        <5> SUFFICES ASSUME NEW gp2 \in Learners, NEW mp2 \in TranClosure(mset), B(mp2) < b
                     PROVE ~BadOneB(gp2, mp2, lobal)
          OBVIOUS
        <5>mp2Msg. mp2 \in Messages  BY <1>mi, TranClosureClosed
        <5>bmp2nat. B(mp2) \in Nat
          <6>1. B(mp2) \in Ballots  BY <1>mi, <5>mp2Msg, BBallot
          <6> QED BY <6>1 DEF Ballots
        <5>k. B(mp2) \in 0..(b-1)  BY <5>bmp2nat
        <5>qk. Q(B(mp2))  BY <5>k
        <5> QED BY <5>qk
      <4>bBallots. b \in Ballots  BY DEF Ballots
      <4>lt. lobal + 1 < b  BY <3>c
      <4> QED BY <4>bBallots, <4>lt, <4>ih, WidthUnexcusableStep
    <3> QED BY <3>a, <3>b, <3>c, <3>mpBnat, <3>lobalNat
  <2> QED BY <2>ind, GeneralNatInduction, IsaM("blast")
<1>fdi. ~Fresh(beta, rstar)
  <2> SUFFICES ASSUME Fresh(beta, rstar) PROVE FALSE  OBVIOUS
  <2>badoneb. BadOneB(beta, rstar, lobal)
    <3>1. lobal < B(rstar)  BY <1>rstarBal
    <3>2. x0 \in Tran(rstar) /\ B(x0) = lobal /\ V(x0) # V(rstar) /\ beta \in Lrns(x0)
      BY <1>x0Tran, <1>x0lobal, <1>Vdiff, <1>wgLrns
    <3>3. \E wg \in Tran(rstar) : B(wg) = lobal /\ V(wg) # V(rstar) /\ beta \in Lrns(wg)
      BY <3>2
    <3> QED BY <3>1, <3>3, <1>selfconn, <1>isOneB DEF BadOneB
  <2> QED BY <2>badoneb, <1>contra
<1> QED BY <1>fdi, <1>qof

====================================================================
