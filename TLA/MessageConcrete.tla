------------------------- MODULE MessageConcrete -------------------------
\* A concrete Messages construction, generic over ValueInterface and
\* LearnerGraphInterface (their record CONSTANTs are left abstract), proving
\* MessageInterfaceAssumptions for the resulting instantiation of
\* MessageInterface.  The construction is extremely close to HPaxos.tla's
\* Message (not MessageCandidate): a level-indexed fixpoint of records
\* [sender, payload, priors] filtered down by a WellFormed predicate.  Most
\* of the "Interface-land" macros (Tran, Refs, Sig, B, V, HasDepth, Fresh,
\* Qd, Lrns, Caught, Con, ...) are necessarily duplicated here in
\* "Concrete-land" form, operating directly on the record structure instead
\* of through the abstract MessageInterface record's raw fields.
\*
\* All four LOCAL INSTANCEs of the original are dropped:
\*   - FiniteSets and FiniteSetsExt CANNOT be LOCAL INSTANCE here. IsFiniteSet
\*     occurs in CMCLNew, Cardinality in CIsOneB, Min in CMinLevel and Max in
\*     CB -- all EXPORTED definition bodies on the CMI dependency path. A
\*     private copy would make every lemma module that unfolds them see
\*     IsFiniteSet_1 / Min_1 / Max_1. They are not re-listed either: both
\*     arrive transitively, as ONE shared copy, via
\*     MessageInterface -> LearnerGraphInterface -> FiniteSetsExt -> FiniteSets.
\*   - FiniteSetTheorems (FS_*) and NaturalsInduction (NatInduction,
\*     GeneralNatInduction, RecursiveFcnOfNat) appear only inside proofs, never
\*     in a definition body, so they are EXTENDS'd by just the lemma modules
\*     that cite them.
EXTENDS MessageInterface

\* ---- the concrete model: message candidates (mirrors HPaxos.tla) ----
\* Senders is Acceptors plus one extra "proposer" identity, guaranteed
\* distinct from every acceptor (via a Russell's-paradox-style existence
\* argument: no set can contain everything).  AlwaysANewProposal has no
\* sender-related side condition, but WellFormed's "an acceptor may not
\* catch itself" clause means a freshly-constructed proposal cannot safely
\* be attributed to an arbitrary (possibly already-caught) acceptor; the
\* extra non-acceptor identity sidesteps that clause entirely, with no need
\* for a third abstract CONSTANT (stays generic over ValueInterface and
\* LearnerGraphInterface only, per the original brief).
CProposerSender == CHOOSE x : x \notin Acceptors

CSenders == Acceptors \cup {CProposerSender}
CProposal == {[type |-> "proposal", ballot |-> b] : b \in Ballots}
CReply == {[type |-> "reply"]}
CPayload == CProposal \cup CReply

CMCLBase == {[sender |-> r[1], payload |-> r[2], priors |-> {}] : r \in CSenders \X CPayload}
CMCLNew(prev) ==
  {[sender |-> r[1], payload |-> r[2], priors |-> r[3]] :
   r \in CSenders \X CPayload \X {x \in SUBSET prev : IsFiniteSet(x)}}
CMCLExt(prev) == prev \cup CMCLNew(prev)
CMCAL[l \in Nat] == IF l = 0 THEN CMCLBase ELSE CMCLExt(CMCAL[l-1])
CMC == UNION {CMCAL[l] : l \in Nat}
CMinLevel(m) == Min({l \in Nat : m \in CMCAL[l]})

CRecursiveFunc(F(_,_), R(_), m) ==
  LET g[l \in Nat] == [x \in CMCAL[l] |->
         F(x, IF l=0 THEN {} ELSE {g[l-1][y] : y \in R(x)})
      ]
   IN g[CMinLevel(m)][m]

CTranR(m, tran_rec_priors) == {m} \cup UNION tran_rec_priors
CPriors(m) == m.priors

CTran(m) == CRecursiveFunc(CTranR, CPriors, m)
CTranExcl(m) == {x \in CTran(m) : x # m}

CRefs(m) == {x \in CTranExcl(m) :
            (\A y \in CTranExcl(m): y = x \/ x \notin CTran(y))}

CIsProposal(m) == m.payload \in CProposal

CB(m) == Max({x.payload.ballot : x \in {y \in CTran(m) : CIsProposal(y)}})

CSig(m) == m.sender
CSigS(S) == {CSig(x) : x \in S}

CV(m) == BalToVal(CB(m))

\* Mirrors MessageInterface's IsOneB.  The abstract interface exposes no "reply"
\* concept, so IsOneB is "not a proposal, with exactly two same-ballot messages
\* in its closure"; on CMessages, m \notin Proposals <=> ~CIsProposal(m), so we
\* use ~CIsProposal here (CProposals is not yet in scope -- it depends on
\* CMessages, which depends on this).  Keeping CIsOneB in lockstep with abstract
\* IsOneB is required for CHasDepth to match the abstract HasDepth.
CIsOneB(m) == ~CIsProposal(m) /\ Cardinality({x \in CTran(m) : CB(x) = CB(m)}) = 2

CCaughtS(S) == {a \in Acceptors:
  \E m1 \in S : \E m2 \in S:
    /\ CSig(m1) = a
    /\ CSig(m2) = a
    /\ m1 \notin CTran(m2)
    /\ m2 \notin CTran(m1)}
CCaught(m) == CCaughtS(CTran(m))
CCon(alpha, x) == ConFromCaught(alpha, CCaught(x))

\* Duplicated from MessageInterface.tla's CombinedFreshQdLrnsIdR, operating
\* on the raw record structure instead of the abstract .tran/.sig fields.
CCflR(x, r) ==
  LET qdx == [pr \in Learners \X Nat |->
       LET alpha == pr[1]
           d     == pr[2]
       IN  {y.id: y \in {mm \in r:
     /\ d > 0
     /\ CB(mm.id) = CB(x)
     /\ CSig(mm.id) \in Acceptors
     /\ d = 1 => (CIsOneB(mm.id) /\ mm.fresh[alpha])
     /\ d > 1 => CSigS(mm.qd[<<alpha, d-1>>]) \in Quorums(alpha)
     }}]
  IN
  [ id |-> x,
    qd |-> qdx,
    lrns  |-> {alpha \in Learners:
                 CSig(x) \in Acceptors /\ CSigS(qdx[<<alpha, 1>>]) \in Quorums(alpha)},
    fresh |-> [alpha \in Learners |->
      \A mm \in r:
        \/ CV(mm.id) = CV(x)
        \/ CCon(alpha, x) \cap mm.lrns = {}
        \/ \E p \in r:
          /\ CB(p.id) > CB(mm.id)
          /\ CCon(alpha, x) \cap p.lrns # {}
    ]
  ]

CCfl(x) == CRecursiveFunc(CCflR, CTranExcl, x)

CHasDepth(alpha, x, d) == CSig(x) \in Acceptors /\
  IF d=0 THEN (CIsOneB(x) /\ CCfl(x).fresh[alpha])
         ELSE CSigS(CCfl(x).qd[<<alpha, d>>]) \in Quorums(alpha)

\* Mirrors MessageInterface's IsTwoA: not a proposal, with depth 1 for some
\* learner (~CIsProposal stands in for m \notin Proposals, as in CIsOneB).
CIsTwoA(m) ==
  /\ ~CIsProposal(m)
  /\ \E alpha \in Learners: CHasDepth(alpha, m, 1)

\* NOTE: CFilterOut deliberately does NOT require m.priors = CRefs(m).
\* Priors-canonicality is not decidable from bounded memos when a prior's
\* signer has equivocated, so it cannot be part of the check an acceptor
\* runs; instead it holds for every message a SAFE acceptor sends, as an
\* invariant of HPaxosPlusCalConcrete (CSafeSentCanonical / CJoint).
CFilterOut(m) ==
  CIsProposal(m) => CB(m) = m.payload.ballot

CWellFormed(m) ==
  /\ \E a \in CTran(m) : CIsProposal(a)
  /\ CSig(m) \in Acceptors => CSig(m) \notin CCaught(m)
  /\ CIsProposal(m) \/ CIsOneB(m) \/ CIsTwoA(m)
  /\ CFilterOut(m)

CMessages == {m \in CMC : (\A x \in CTran(m): CWellFormed(x))}

CProposals == {m \in CMessages : CIsProposal(m)}
CProposalBalField == [p \in CProposals |-> p.payload.ballot]
CSigField == [m \in CMessages |-> CSig(m)]
CTranField == [m \in CMessages |-> CTranExcl(m)]

CMI == [messages |-> CMessages, proposals |-> CProposals, senders |-> CSenders,
        sig |-> CSigField, proposalbal |-> CProposalBalField, tran |-> CTranField]

\* ===================================================================
\* The following are NOT needed to define CMI; they are defined here only
\* for use in the lemmas, which now live in their own modules.
\* ===================================================================

\* CGFun / CGRec / CQPred: the explicit CHOOSE-form of the level-indexed
\* recursion that CRecursiveFunc builds with a LET, plus its step predicate.
\* Only the recursion lemmas (CRMFViaG, CGStep, CLevelIndepGen, ...) mention them.
CGFun(F(_,_), R(_)) == CHOOSE g : g = [l \in Nat |->
    [x \in CMCAL[l] |->
       F(x, IF l = 0 THEN {} ELSE {g[l-1][y] : y \in R(x)})]]

CGRec(g, F(_,_), R(_)) ==
  \A l \in Nat : \A x \in CMCAL[l] :
    g[l][x] = F(x, IF l = 0 THEN {} ELSE {g[l-1][y] : y \in R(x)})

CQPred(g, n) == \A x \in CMCAL[n] :
                 g[n][x] = g[CMinLevel(x)][x]

\* Induction carrier for CTranLevelLE.
CTranBelowProp(x) == \A y \in CTran(x) :
                      y \in CMC /\ CMinLevel(y) <= CMinLevel(x)

\* Dual of CIsProposal; used only to discharge "not a proposal" side conditions.
CIsReply(m) == m.payload \in CReply

\* "maximal antichain within U"; used only by CGenTranRefs and its consumers.
CMMax(U) == {x \in U : \A y \in U : x \notin CTranExcl(y)}
=============================================================================
