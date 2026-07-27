-------------------------- MODULE MessageInterface --------------------------
\* Definitions and assumptions only (lines 1-275 of the unsplit module); every
\* lemma and theorem lives in its own module.
\*
\* EXTENDS, not LOCAL INSTANCE, throughout. Cardinality / IsFiniteSet / Max
\* appear in the bodies of EXPORTED definitions here (IsOneB,
\* MessagesWithTranSizeAtMost, RecursiveMessage*Func, B), so every consumer
\* that unfolds one of those definitions must see the SAME copy of them.
\* LOCAL INSTANCE would hand this module private copies, SANY would rename
\* them apart, and consumer proofs would fail. EXTENDS shares; INSTANCE copies.
\*
\*   ValueInterface          -> Ballots, BalToVal (and Naturals)
\*   LearnerGraphInterface   -> Acceptors, Learners, Quorums, ConFromCaught,
\*                              MaxDepth, and transitively FiniteSetsExt
\*                              (Max, IsFiniteSet, Cardinality, Integers)
\*                              and Sequences
\*
\* Dropped from the unsplit header, all proof-only and so unused here:
\* FiniteSetTheorems (FS_*), NaturalsInduction, SequenceTheorems. FiniteSets
\* and FiniteSetsExt are dropped as separate lines because
\* LearnerGraphInterface already re-exports them -- naming them again would be
\* redundant, not wrong.
EXTENDS ValueInterface, LearnerGraphInterface

CONSTANT MessageInterface


\* defining the relevant macros
Messages == MessageInterface.messages
Proposals == MessageInterface.proposals
Senders == MessageInterface.senders
Sig(m) == MessageInterface.sig[m]
ProposalBal(m) == MessageInterface.proposalbal[m]
\* rather than assuming tran is reflexive, we just define it that way
Tran(m) == {m} \cup MessageInterface.tran[m]

\* some more macros that only use the above macros
TranExclusive(m) == Tran(m) \ {m}

\* The Tran-closure of a set of messages: m together with every ancestor of
\* every element of m.  Used as the target of TranExclusive(x) = ... in the
\* AlwaysANew* assumptions below, since TranExclusive(x) is itself always
\* Tran-closed (by TranTrans) -- so a raw, possibly non-closed m could never
\* be matched exactly.
TranClosure(m) == UNION {Tran(x) : x \in m}

Refs(m) == {x \in TranExclusive(m) :
            \A y \in TranExclusive(m) : x \notin TranExclusive(y)}

SigS(m) == {Sig(x) : x \in m}

GetProposals(m) == Proposals \cap Tran(m)

B(m) == Max({ProposalBal(x) : x \in GetProposals(m)})
V(m) == BalToVal(B(m))

IsProposal(m) == m \in Proposals

\* OneB messages are precisely those that reply to a 1A and nothing else
\* Under this definition, they can themselves be a 1a,
\*  just not one with a higher ballot.
\* We can choose to change that if we want.
IsOneB(m) == ~IsProposal(m) /\ Cardinality({x \in Tran(m): B(x)=B(m)}) = 2

\* caught acceptors as of a set of messages are those who have sent two messages, neither of which is in the transitive history of the other.
CaughtS(m) == {a \in Acceptors:
  \E m1 \in m : \E m2 \in m:
    /\ Sig(m1) = a
    /\ Sig(m2) = a
    /\ m1 \notin Tran(m2)
    /\ m2 \notin Tran(m1)}

\* caught acceptors as of a message are those who have sent two messages in its transitive history, neither of which is in the transitive history of the other.
Caught(m) == CaughtS(Tran(m))

\* Learners connected to alpha as of message x
\* there is at least one safety set with no member caught as of x
Con(alpha, x) == ConFromCaught(alpha, Caught(x))


\* some machinery that's useful for recursive definitions
MessagesWithTranSizeAtMost(n) == {x \in Messages : Cardinality(Tran(x)) <= n}
RecursiveMessageRefsFunc(F(_,_), m) ==
  LET g[l \in Nat] == [x \in MessagesWithTranSizeAtMost(l) |->
         F(x, IF l=0 THEN {} ELSE {g[l-1][y] : y \in Refs(x)})]
   IN g[Cardinality(Tran(m))][m]
RecursiveMessageTranFunc(F(_,_), m) ==
  LET g[l \in Nat] == [x \in MessagesWithTranSizeAtMost(l) |->
         F(x, IF l=0 THEN {} ELSE {g[l-1][y] : y \in TranExclusive(x)})]
   IN g[Cardinality(Tran(m))][m]

\* used only for HasDepth definition (which requires recursion)
CombinedFreshQdLrnsIdR(x, r) ==
  LET qdx == [pr \in Learners \X Nat |->
       LET alpha == pr[1]
           d     == pr[2]
       IN  {y.id: y \in {m \in r:
     /\ d > 0
     /\ B(m.id) = B(x)
     /\ Sig(m.id) \in Acceptors
     /\ d = 1 => (IsOneB(m.id) /\ m.fresh[alpha])
     /\ d > 1 => SigS(m.qd[<<alpha, d-1>>]) \in Quorums(alpha)
     }}]
  IN
  [ id |-> x,
    qd |-> qdx,
    lrns  |-> {alpha \in Learners:
                 Sig(x) \in Acceptors /\ SigS(qdx[<<alpha, 1>>]) \in Quorums(alpha)},
    fresh |-> [alpha \in Learners |->
      \A m \in r:
        \/ V(m.id) = V(x)
        \/ Con(alpha, x) \cap m.lrns = {}
        \/ \E p \in r:
          /\ B(p.id) > B(m.id)
          /\ Con(alpha, x) \cap p.lrns # {}
    ]
  ]
CombinedFreshQdLrnsId(x) == RecursiveMessageTranFunc(CombinedFreshQdLrnsIdR, x)


\* We later prove HasDepth is
\* LEMMA HasDepthDef ==
\*   HasDepth(alpha, x, d) =
\*     /\ Sig(x) \in Acceptors
\*     /\ IF d=0 THEN (IsOneB(x) /\ Fresh(alpha, x))
\*               ELSE SigS(Qd(alpha, x, d)) \in Quorums(alpha)
\* but for mutual recursion reasons, we have to define it like this:
HasDepth(alpha, x, d) == Sig(x) \in Acceptors /\
  IF d=0 THEN (IsOneB(x) /\ CombinedFreshQdLrnsId(x).fresh[alpha])
         ELSE SigS(CombinedFreshQdLrnsId(x).qd[<<alpha, d>>]) \in Quorums(alpha)

Lrns(m) == {alpha \in Learners : HasDepth(alpha, m, 1)}
\* A 1b is fresh precisely when its value agrees with the value of the
\* highest-ballot referenced message that carries a connected learner
\* (paper Definition 17): every referenced message either agrees in value,
\* or carries NO connected learner (irrelevant), or is superseded by a
\* higher-ballot message that does carry a connected learner.
Fresh(alpha, m) ==
  \A x \in Tran(m) :
    \/ V(x) = V(m)
    \/ Con(alpha, m) \cap Lrns(x) = {}
    \/ \E p \in TranExclusive(m) :
      /\ B(p) > B(x)
      /\ Con(alpha, m) \cap Lrns(p) # {}
Qd(alpha, m, d) ==
  {x \in TranExclusive(m) :
    /\ d > 0
    /\ B(m) = B(x)
    /\ HasDepth(alpha, x, d-1)}



\* TwoAs must have depth,
\* considered requiring that you must have a message at all prior depths,
\* but I don't think that's necessary.
\* not sure if that last part is necessary
IsTwoA(m) == ~IsProposal(m) /\ \E alpha \in Learners: HasDepth(alpha,m,1)
\*  /\ \A d \in Nat: \A alpha \in Learners: HasDepth(alpha, m, d) =>
\*     \E x \in TranExclusive(m):
\*       /\ Sig(x) = Sig(m)
\*       /\ B(x) = B(m)
\*       /\ HasDepth(alpha, x, d-1)

\* The previous message(s) by m's signer: same-signature strict ancestors that
\* are maximal AMONG SAME-SIGNATURE elements (not below any other same-sig
\* message in m's strict closure).
Prev(m) == {x \in TranExclusive(m) :
  /\ Sig(x) = Sig(m)
  /\ \A y \in TranExclusive(m): (x \in TranExclusive(y) => Sig(x) # Sig(y))}

DecisionSlow(m, alpha, b) ==
  SigS({x \in TranClosure(m) : B(x) = b /\ HasDepth(alpha, x, MaxDepth(alpha))
       }) \in Quorums(alpha)

\* Fast decision: a set of ballot-b messages that carries an l-quorum of
\* l-attesting messages both for alpha itself and for every learner l still
\* connected to alpha via any of them.  Including alpha in the quantifier
\* anchors the decision (without it, s = {} satisfies the \A vacuously);
\* the connected learners' quorums substitute for depth in the agreement
\* chain argument.
DecisionFast(m, alpha, b) ==
  \E s \in SUBSET {x \in TranClosure(m) : B(x) = b} :
  LET L == ({alpha} \cup UNION {Con(alpha, x) : x \in s})
   IN /\ \A l \in L : SigS(s) \in Quorums(l)
      /\ \A x \in s :
        /\ L \subseteq Lrns(x)
        /\ \A l \in L :
           SigS({y \in TranExclusive(x) :
                 B(y) = b /\ L \subseteq Lrns(y)}) \in Quorums(l)

\* Extreme version of decisionFast
\* assumes there is a learner l whose only quorum is the set of all Acceptors
\* but this is meant to be a decision for any learner, not just l.
\* We're just using "l" to make construction here more convenient.
\* true when there is some depth-d 2a message "x" such that:
\*   it has ballot b
\*   no earlier messages have any other ballot (b is earliest)
\*   no one is caught
\* this is similar to DecisionFast above for d=3, I think
\* it implies d-1 "rounds" of all learners sending a 2a.
\*
\* We'll want to try to figure out if this works as a decision procedure for any constant d, or more extreme, for any d such that some learner has maxdepth greater than d.
\* This is something we want to try eventually, but perhaps in the short term, it's more important to work on liveness.
DecisionFastD(m,b, d) ==
  \E l \in Learners :
  /\ Quorums(l) = {Acceptors}
  /\ \E x \in SUBSET TranClosure(m) :
     /\ Caught(x) = {}
     /\ \A y \in Tran(x) : B(y) = b
     /\ HasDepth(l, x, d)



\* The fast path is REFUTED -- "connectivity laundering" countermodel,
\* machine-checked in TLCLaunder.tla (graph TLAPS-verified in
\* XFastCE3Graph.tla); see DecisionFastSoundness.md.  Decision is therefore
\* the slow rule only; DecisionFast stays defined above solely as the record
\* of the refuted rule (XFastProof.tla and the countermodel reference it).
Decision(m, alpha, b) == DecisionSlow(m, alpha, b)


\* assumptions

TypeOKMessageInterface ==
    /\ MessageInterface.tran \in [Messages -> SUBSET Messages]
    /\ MessageInterface.sig \in [Messages -> Senders]
    /\ Proposals \subseteq Messages
    /\ MessageInterface.proposalbal \in [Proposals -> Ballots]
TranFinite == \A m \in Messages: IsFiniteSet(Tran(m))
TranTrans == \A m \in Messages: \A x \in Tran(m) : Tran(x) \subseteq Tran(m)
TranAcyclic == \A m \in Messages : \A x \in TranExclusive(m): m \notin Tran(x)
AlwaysAProposal == \A m \in Messages: GetProposals(m) # {}
AlwaysANewProposal == \A m \in SUBSET Messages: \A b \in Ballots:
  (/\ IsFiniteSet(m)
   /\ \A x \in m: B(x) < b
   ) =>  \E p \in Proposals:
     (/\ TranExclusive(p) = TranClosure(m)
      /\ B(p) = b
      /\ Sig(p) \notin Acceptors)
AlwaysANewOneB ==
  \A m \in SUBSET Messages : \A b \in Ballots: \A a \in Acceptors:
  (/\ IsFiniteSet(m)
   /\ \A x \in m: B(x) <= b
   /\ Cardinality({x \in TranClosure(m) : B(x) = b}) = 1
   /\ a \notin CaughtS(TranClosure(m))
  ) => \E x \in Messages :
    (/\ Sig(x) = a
     /\ a \notin Caught(x)
     /\ IsOneB(x)
     /\ TranExclusive(x) = TranClosure(m))
AlwaysANewTwoA ==
  \A m \in SUBSET Messages :
  \A b \in Ballots:
  \A a \in Acceptors:
  \A alpha \in Learners:
  \A d \in (1..(MaxDepth(alpha))):
  (/\ IsFiniteSet(m)
   /\ \A x \in m: B(x) <= b
   /\ a \notin CaughtS(TranClosure(m))
   /\ SigS({x \in TranClosure(m):
            B(x) = b /\ HasDepth(alpha, x, d-1)}) \in Quorums(alpha)
\*          \* a's own ballot-b prior 2A at depth d-1 already exists in the closure (its
\*          \* whole same-signer chain does too, by IsTwoA), so the depth-d witness we
\*          \* build can satisfy IsTwoA's same-signer prior-depth requirement.
\*          /\ \E p \in TranClosure(m):
\*               /\ Sig(p) = a
\*               /\ B(p) = b
\*               /\ HasDepth(alpha, p, d-1)
\*               /\ IsTwoA(p)
  ) => \E x \in Messages:
  (/\ x \in TranClosure(m) \/ TranClosure(m) = TranExclusive(x)
   /\ B(x) = b
   /\ Sig(x) = a
   /\ HasDepth(alpha, x, d)
   /\ a \notin Caught(x)
   /\ IsTwoA(x))

AcceptorsSubsetSenders == Acceptors \subseteq Senders
MessageInterfaceAssumptions ==
    /\ TypeOKMessageInterface
    /\ TranFinite
    /\ TranTrans
    /\ TranAcyclic
    /\ AlwaysAProposal
    /\ AlwaysANewProposal
    /\ AlwaysANewOneB
    /\ AlwaysANewTwoA
    /\ AcceptorsSubsetSenders


\* ==========================================================================
\* Defined for use in lemmas
\* ==========================================================================
\* These appear part-way through the unsplit MessageInterface, each
\* introducing machinery for the lemmas that immediately follow it. They are
\* kept here rather than given their own modules for two reasons:
\*   - Every lemma module that unfolds one of them would otherwise have to
\*     EXTENDS its module, deepening an already long import chain without
\*     changing what any proof can see.
\*   - Several are HIGHER-ORDER -- GFunMI and GRecMI take operator arguments
\*     -- and TLAPS instantiates operator arguments poorly across module
\*     boundaries. TranCard exists specifically to dodge a related problem
\*     (TLAPS cannot instantiate the anonymous lambda
\*     y |-> Cardinality(Tran(y)), only a named operator), so its name must
\*     stay visible to every call site.

GFunMI(F(_,_), R(_)) ==
  CHOOSE g : g = [l \in Nat |->
    [x \in MessagesWithTranSizeAtMost(l) |->
       F(x, IF l = 0 THEN {} ELSE {g[l-1][y] : y \in R(x)})]]

\* g satisfies the recursive equation (abstracted from the CHOOSE).
GRecMI(g, F(_,_), R(_)) ==
  \A l \in Nat : \A x \in MessagesWithTranSizeAtMost(l) :
    g[l][x] = F(x, IF l = 0 THEN {} ELSE {g[l-1][y] : y \in R(x)})

\* (TLAPS can instantiate the operator argument f with a named operator, but not
\* with the anonymous lambda y |-> Cardinality(Tran(y))).
TranCard(mm) == Cardinality(Tran(mm))

\* --- trace machinery -----------------------------------------------

TraceElem == [mm : Messages, rr : Messages, ss : Messages, gamma : Learners]

\* The core trace conditions (paper Lemma 25 items 1-15 minus the depth
\* budget, item 12, which differs between slow and fast decisions and is
\* deliberately excluded from the minimality predicate).
\*   alpha : the low-ballot deciding learner
\*   lobal : its decision ballot (B(S_alpha) in the paper)
\*   CL    : the ambient Tran-closed carrier, TranClosure(mset)
\*   himsg : the high-ballot message from the other decision (m in the paper)
TraceCondCore(alpha, lobal, CL, himsg, seq, x) ==
  LET mm    == seq[x].mm
      rr    == seq[x].rr
      ss    == seq[x].ss
      gamma == seq[x].gamma
  IN
  /\ mm \in Tran(himsg)                                        \* paper: m_x \in Tran(m)
  /\ x = 1 => gamma \in ConFromCaught(alpha, CaughtS(CL))      \* item 1 (entangled-in-closure)
  /\ lobal < B(mm)                                             \* item 2
  \* item 3: mm strictly shrinks in Tran-DAG depth, not ballot -- ballots
  \* legitimately repeat across a single TwoA's whole depth-tree (Qd forces
  \* B(m)=B(x) one level down), so ballot can't be the well-founded measure.
  \* Cardinality(Tran(.)) always strictly decreases (TranAcyclic), for free.
  /\ x > 1 => Cardinality(Tran(mm)) < Cardinality(Tran(seq[x-1].mm))  \* item 3
  /\ x > 1 => mm \in Tran(seq[x-1].rr)                         \* item 4
  /\ x > 1 => gamma \in Con(alpha, seq[x-1].rr)                \* item 5
  /\ x > 2 => gamma \notin Con(alpha, seq[x-2].rr)             \* item 6
  /\ gamma \in Lrns(mm)                                        \* item 7
  /\ rr \in Qd(gamma, mm, 1)                                   \* item 8
  /\ ss \in Tran(rr)                                           \* item 9
  /\ x > 1 => ss \in Tran(seq[x-1].ss)                         \* item 10
  /\ Sig(rr) = Sig(ss)                                         \* item 11
  /\ B(ss) = lobal                                             \* item 13
  /\ V(mm) = V(himsg)                                          \* item 14

\* Item 15: mm_x is a LOWEST-Tran-Cardinality message admitting the core
\* conditions at its index (replacing the element by any other candidate
\* cannot lower Cardinality(Tran(mm)) -- matches item 3's measure, not
\* ballot).  Minimality ranges over the core only -- NOT the budget -- so
\* that the gamma_2 minimality argument in TraceContradiction can compare
\* against candidates whose support message is drawn from a later level.
TraceCondCoreMin(alpha, lobal, CL, himsg, seq, x) ==
  /\ TraceCondCore(alpha, lobal, CL, himsg, seq, x)
  /\ \A z \in TraceElem :
       TraceCondCore(alpha, lobal, CL, himsg, [seq EXCEPT ![x] = z], x)
         => Cardinality(Tran(seq[x].mm)) <= Cardinality(Tran(z.mm))

\* Item 12, slow variant: the support message still has MaxDepth(alpha)-x+1
\* depth levels of alpha-quorums remaining (one is consumed per chain step).
TraceBudgetSlow(alpha, seq, x) ==
  x <= MaxDepth(alpha) => HasDepth(alpha, seq[x].ss, MaxDepth(alpha) - x + 1)

\* --- witness constructors ------------------------------------------

IdOp(n) == n

\* --- per-learner top witness (concrete predicate) ---
TopLearnerMsg(mm, beta) ==
  CHOOSE x \in TranClosure(mm) :
    beta \in Lrns(x) /\ (\A y \in TranClosure(mm) : beta \in Lrns(y) => B(y) <= B(x))

\* --- catch-witness pair (concrete, non-higher-order) ---
CatchWitness1(mm, s) ==
  CHOOSE x \in TranClosure(mm) :
    \E y \in TranClosure(mm) :
      /\ Sig(x) = s /\ Sig(y) = s
      /\ x \notin Tran(y) /\ y \notin Tran(x)
CatchWitness2(mm, s) ==
  CHOOSE y \in TranClosure(mm) :
    /\ Sig(CatchWitness1(mm,s)) = s /\ Sig(y) = s
    /\ CatchWitness1(mm,s) \notin Tran(y) /\ y \notin Tran(CatchWitness1(mm,s))

\* (a) catch witnesses (so oneb doesn't LOSE any existing catch) and
\* (b) per-learner top-ballot witnesses (for the Fresh clause-(c) chain argument).
CaughtAcc(mm) == CaughtS(TranClosure(mm))
RelevantLearners(mm) == {beta \in Learners : \E x \in TranClosure(mm) : beta \in Lrns(x)}

CQ(mm) ==
  {CatchWitness1(mm,s) : s \in CaughtAcc(mm)}
  \cup {CatchWitness2(mm,s) : s \in CaughtAcc(mm)}
  \cup {TopLearnerMsg(mm,beta) : beta \in RelevantLearners(mm)}

\* --- picking beta*: the globally top-ballot per-learner witness ---
BXBeta(mm, beta) == B(TopLearnerMsg(mm, beta))

DecideableProposalTranExclusive(mm) == TranClosure(CQ(mm))

DecideableProposalV(alpha, bal, mm) ==
  LET S  == ConFromCaught(alpha, CaughtS(TranClosure(mm)))
      SS == S \cap RelevantLearners(mm)
  IN  IF SS = {}
      THEN BalToVal(bal)
      ELSE LET betastar == CHOOSE beta \in SS : \A gamma \in SS : BXBeta(mm,gamma) <= BXBeta(mm,beta)
           IN V(TopLearnerMsg(mm, betastar))
====================================================================
