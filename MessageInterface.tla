-------------------------- MODULE MessageInterface --------------------------
EXTENDS ValueInterface, LearnerGraphInterface
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE FiniteSetsExt
LOCAL INSTANCE FiniteSetTheorems
LOCAL INSTANCE NaturalsInduction
LOCAL INSTANCE SequenceTheorems

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

MaxProposals(m) == {x \in GetProposals(m) : ProposalBal(x) = B(m)}

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
\* machine-checked in TLCLaunder.tla; see DecisionFastSoundness.md.
\* Decision is therefore
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




\* ===================================================================
\* Helper lemmas
\* ===================================================================

\* Every message in the transitive closure of m is itself a message.
LEMMA TranSubMessages ==
    ASSUME TypeOKMessageInterface, NEW x \in Messages
    PROVE Tran(x) \subseteq Messages
<1>1. MessageInterface.tran \in [Messages -> SUBSET Messages]
    BY DEF TypeOKMessageInterface
<1>2. MessageInterface.tran[x] \subseteq Messages  BY <1>1
<1> QED BY <1>2 DEF Tran

\* The transitive closure of any message is a finite set with a Nat cardinality.
LEMMA TranCardNat ==
    ASSUME TranFinite, NEW x \in Messages
    PROVE  /\ IsFiniteSet(Tran(x))
           /\ Cardinality(Tran(x)) \in Nat
<1>1. IsFiniteSet(Tran(x))  BY DEF TranFinite
<1> QED BY <1>1, FS_CardinalityType

\* A finite non-empty set has an element maximizing any Nat-valued function.
LEMMA FiniteMaxExists ==
    ASSUME NEW S, IsFiniteSet(S), S # {}, NEW f(_),
           \A x \in S : f(x) \in Nat
    PROVE \E r \in S : \A y \in S : f(y) <= f(r)
<1> DEFINE Q(n) == \A U : (IsFiniteSet(U) /\ Cardinality(U) = n /\ U # {}
                            /\ (\A z \in U : f(z) \in Nat))
                          => (\E r \in U : \A y \in U : f(y) <= f(r))
<1> SUFFICES \A n \in Nat : Q(n)
  <2>1. Cardinality(S) \in Nat  BY FS_CardinalityType
  <2> QED BY <2>1 DEF Q
<1> HIDE DEF Q
<1>ind. \A n \in Nat : (\A k \in 0..(n-1) : Q(k)) => Q(n)
  <2> USE DEF Q
  <2> SUFFICES ASSUME NEW n \in Nat, \A k \in 0..(n-1) : Q(k),
                      NEW U, IsFiniteSet(U), Cardinality(U) = n, U # {},
                      \A z \in U : f(z) \in Nat
               PROVE  \E r \in U : \A y \in U : f(y) <= f(r)
    OBVIOUS
  <2>x. PICK x \in U : TRUE  OBVIOUS
  <2>fx. f(x) \in Nat  BY <2>x
  <2>pos. Cardinality(U) >= 1  BY FS_EmptySet, FS_CardinalityType
  <2>n1. n - 1 \in Nat  BY <2>pos
  <2>U2. IsFiniteSet(U \ {x}) /\ Cardinality(U \ {x}) = n - 1
    BY <2>x, FS_RemoveElement
  <2>1. CASE U \ {x} = {}
    <3>1. \A y \in U : f(y) <= f(x)
      <4>1. ASSUME NEW y \in U PROVE f(y) <= f(x)
        <5>1. y = x  BY <2>1, <4>1
        <5> QED BY <5>1, <2>fx
      <4> QED BY <4>1
    <3> QED BY <3>1, <2>x
  <2>2. CASE U \ {x} # {}
    <3>k. n - 1 \in 0..(n-1)  BY <2>n1
    <3>z. \A z \in U \ {x} : f(z) \in Nat  OBVIOUS
    <3>IH. \E r \in U \ {x} : \A y \in U \ {x} : f(y) <= f(r)
      <4>1. Q(n-1)  BY <3>k
      <4> QED BY <4>1, <2>U2, <2>2, <3>z
    <3>r. PICK r \in U \ {x} : \A y \in U \ {x} : f(y) <= f(r)  BY <3>IH
    <3>rU. r \in U  BY <3>r
    <3>fr. f(r) \in Nat  BY <3>rU
    <3>1. CASE f(x) <= f(r)
      <4>1. \A y \in U : f(y) <= f(r)
        <5>1. ASSUME NEW y \in U PROVE f(y) <= f(r)
          <6>1. CASE y = x  BY <6>1, <3>1
          <6>2. CASE y # x  BY <6>2, <3>r
          <6> QED BY <6>1, <6>2
        <5> QED BY <5>1
      <4> QED BY <4>1, <3>rU
    <3>2. CASE ~(f(x) <= f(r))
      <4>1. \A y \in U : f(y) <= f(x)
        <5>1. ASSUME NEW y \in U PROVE f(y) <= f(x)
          <6>1. CASE y = x  BY <6>1, <2>fx
          <6>2. CASE y # x
            <7>1. y \in U \ {x}  BY <6>2
            <7>2. f(y) <= f(r) /\ f(y) \in Nat  BY <7>1, <3>r
            <7> QED BY <7>2, <3>fr, <2>fx, <3>2
          <6> QED BY <6>1, <6>2
        <5> QED BY <5>1
      <4> QED BY <4>1, <2>x
    <3> QED BY <3>1, <3>2
  <2> QED BY <2>1, <2>2
<1> QED BY <1>ind, GeneralNatInduction, IsaM("blast")

\* ===================================================================

LEMMA TranExclusiveDecreasesTranSize ==
    ASSUME TranTrans, TranFinite, TranAcyclic,
           NEW m \in Messages,
           NEW x \in TranExclusive(m)
    PROVE Cardinality(Tran(m)) > Cardinality(Tran(x))
<1>1. x \in Tran(m) /\ x # m  BY DEF TranExclusive
<1>2. Tran(x) \subseteq Tran(m)  BY <1>1 DEF TranTrans
<1>3. IsFiniteSet(Tran(m))  BY DEF TranFinite
<1>4. m \in Tran(m)  BY DEF Tran
<1>5. m \notin Tran(x)  BY <1>1 DEF TranAcyclic
<1>6. Tran(m) # Tran(x)  BY <1>4, <1>5
<1>7. Cardinality(Tran(x)) <= Cardinality(Tran(m))  BY <1>2, <1>3, FS_Subset
<1>8. Cardinality(Tran(m)) # Cardinality(Tran(x))  BY <1>2, <1>3, <1>6, FS_Subset
<1>9. Cardinality(Tran(x)) \in Nat /\ Cardinality(Tran(m)) \in Nat
    BY <1>2, <1>3, FS_Subset, FS_CardinalityType
<1> QED BY <1>7, <1>8, <1>9

\* ===================================================================
\* Generic well-founded recursion over the Cardinality(Tran(.)) measure.
\* This mirrors the level-based development in HPaxos.tla, but here the
\* well-founded measure is Cardinality(Tran(m)) and the "level-l carrier"
\* is MessagesWithTranSizeAtMost(l).  Instantiating R := TranExclusive
\* recovers RecursiveMessageTranFunc, and R := Refs recovers
\* RecursiveMessageRefsFunc.
\* ===================================================================

\* The recursive function underlying RecursiveMessageTranFunc /
\* RecursiveMessageRefsFunc, lifted to a top-level operator so we can reason
\* about g[l][x] at levels l other than x's own Cardinality(Tran(x)).
GFunMI(F(_,_), R(_)) ==
  CHOOSE g : g = [l \in Nat |->
    [x \in MessagesWithTranSizeAtMost(l) |->
       F(x, IF l = 0 THEN {} ELSE {g[l-1][y] : y \in R(x)})]]

\* g satisfies the recursive equation (abstracted from the CHOOSE).
GRecMI(g, F(_,_), R(_)) ==
  \A l \in Nat : \A x \in MessagesWithTranSizeAtMost(l) :
    g[l][x] = F(x, IF l = 0 THEN {} ELSE {g[l-1][y] : y \in R(x)})

\* The defining equation of GFunMI's inner recursive function, from
\* RecursiveFcnOfNat (the body at level l uses only level l-1).
LEMMA gStepMI ==
  ASSUME NEW F(_,_), NEW R(_), NEW l \in Nat,
         NEW x \in MessagesWithTranSizeAtMost(l)
  PROVE  GFunMI(F, R)[l][x] =
           F(x, IF l = 0 THEN {} ELSE {GFunMI(F, R)[l-1][y] : y \in R(x)})
<1> DEFINE Def(g, k) == [z \in MessagesWithTranSizeAtMost(k) |->
                          F(z, IF k = 0 THEN {} ELSE {g[k-1][w] : w \in R(z)})]
<1> DEFINE gg[k \in Nat] == Def(gg, k)
<1>1. ASSUME NEW k \in Nat, NEW g, NEW h, \A i \in 0..(k-1) : g[i] = h[i]
      PROVE  Def(g, k) = Def(h, k)
  BY <1>1
<1> HIDE DEF Def
<1>2. gg = [k \in Nat |-> Def(gg, k)]  BY <1>1, RecursiveFcnOfNat, Isa
<1>3. gg = GFunMI(F, R)  BY Zenon DEF GFunMI, Def
<1>4. GFunMI(F, R) = [k \in Nat |-> Def(GFunMI(F, R), k)]  BY <1>2, <1>3
<1>5. GFunMI(F, R)[l] = Def(GFunMI(F, R), l)  BY <1>4
<1> QED  BY <1>5 DEF Def

\* Level-independence for an abstract g satisfying the recursion, by
\* course-of-values induction on the Cardinality(Tran(.)) measure.
LEMMA LevelIndepGFunMI ==
  ASSUME TranFinite,
         NEW F(_,_), NEW R(_),
         \A w \in Messages : R(w) \subseteq Messages,
         \A w \in Messages : \A y \in R(w) :
             Cardinality(Tran(y)) < Cardinality(Tran(w)),
         NEW ll \in Nat, NEW xx \in MessagesWithTranSizeAtMost(ll)
  PROVE  GFunMI(F, R)[ll][xx] = GFunMI(F, R)[Cardinality(Tran(xx))][xx]
<1> DEFINE g == GFunMI(F, R)
<1> DEFINE lev(z) == Cardinality(Tran(z))
<1>grec. GRecMI(g, F, R)  BY gStepMI DEF GRecMI
<1> DEFINE Q(n) == \A x \in MessagesWithTranSizeAtMost(n) : g[n][x] = g[lev(x)][x]
<1> SUFFICES \A n \in Nat : Q(n)  BY DEF Q
<1> HIDE DEF Q
<1>ind. \A n \in Nat : (\A mm \in 0..(n-1) : Q(mm)) => Q(n)
  <2> USE DEF Q
  <2> SUFFICES ASSUME NEW n \in Nat, \A mm \in 0..(n-1) : Q(mm),
                      NEW x \in MessagesWithTranSizeAtMost(n)
               PROVE  g[n][x] = g[lev(x)][x]
    OBVIOUS
  <2>mc. x \in Messages /\ lev(x) <= n  BY DEF MessagesWithTranSizeAtMost
  <2>lev. lev(x) \in Nat  BY <2>mc, TranCardNat
  <2>xl. x \in MessagesWithTranSizeAtMost(lev(x))  BY <2>mc, <2>lev DEF MessagesWithTranSizeAtMost
  <2>gn. g[n][x] = F(x, IF n = 0 THEN {} ELSE {g[n-1][y] : y \in R(x)})
    BY <1>grec DEF GRecMI
  <2>gl. g[lev(x)][x] = F(x, IF lev(x) = 0 THEN {} ELSE {g[lev(x)-1][y] : y \in R(x)})
    BY <2>lev, <2>xl, <1>grec DEF GRecMI
  <2> SUFFICES (IF n = 0 THEN {} ELSE {g[n-1][y] : y \in R(x)})
             = (IF lev(x) = 0 THEN {} ELSE {g[lev(x)-1][y] : y \in R(x)})
    BY <2>gn, <2>gl
  <2>R. \A y \in R(x) : y \in Messages /\ lev(y) \in Nat /\ lev(y) < lev(x)
    <3>1. ASSUME NEW y \in R(x)
          PROVE  y \in Messages /\ lev(y) \in Nat /\ lev(y) < lev(x)
      <4>1. y \in Messages   BY <2>mc
      <4>2. lev(y) \in Nat   BY <4>1, TranCardNat
      <4>3. lev(y) < lev(x)  BY <2>mc
      <4> QED BY <4>1, <4>2, <4>3
    <3> QED BY <3>1
  <2>1. CASE n = 0
    <3>1. lev(x) = 0   BY <2>1, <2>mc, <2>lev, SMT
    <3> QED BY <2>1, <3>1
  <2>2. CASE n # 0 /\ lev(x) = 0
    <3>1. R(x) = {}    BY <2>2, <2>R
    <3>2. {g[n-1][y] : y \in R(x)} = {}  BY <3>1
    <3> QED BY <2>2, <3>2
  <2>3. CASE n # 0 /\ lev(x) # 0
    <3>0. /\ n-1 \in Nat /\ lev(x)-1 \in Nat
          /\ n-1 \in 0..(n-1) /\ lev(x)-1 \in 0..(n-1)
      BY <2>3, <2>mc, <2>lev, SMT
    <3>1. {g[n-1][y] : y \in R(x)} = {g[lev(x)-1][y] : y \in R(x)}
      <4>1. ASSUME NEW y \in R(x) PROVE g[n-1][y] = g[lev(x)-1][y]
        <5>1. y \in Messages /\ lev(y) \in Nat /\ lev(y) < lev(x)   BY <2>R
        <5>3. lev(y) <= n-1 /\ lev(y) <= lev(x)-1     BY <5>1, <2>3, <2>mc, <2>lev, <3>0, SMT
        <5>4. y \in MessagesWithTranSizeAtMost(n-1)      BY <5>1, <5>3 DEF MessagesWithTranSizeAtMost
        <5>5. y \in MessagesWithTranSizeAtMost(lev(x)-1) BY <5>1, <5>3 DEF MessagesWithTranSizeAtMost
        <5>8. g[n-1][y] = g[lev(y)][y]                BY <3>0, <5>4
        <5>9. g[lev(x)-1][y] = g[lev(y)][y]           BY <3>0, <5>5
        <5> QED BY <5>8, <5>9
      <4> QED BY <4>1
    <3> QED BY <2>3, <3>1
  <2> QED BY <2>1, <2>2, <2>3
<1> QED BY <1>ind, GeneralNatInduction, IsaM("blast")

\* The recursion equation for GFunMI evaluated at a message's own level.
LEMMA GFunRecMI ==
  ASSUME TranFinite, NEW F(_,_), NEW R(_), NEW m \in Messages,
         \A x \in Messages : R(x) \subseteq Messages,
         \A x \in Messages : \A y \in R(x) :
             Cardinality(Tran(y)) < Cardinality(Tran(x))
  PROVE GFunMI(F, R)[Cardinality(Tran(m))][m]
        = F(m, {GFunMI(F, R)[Cardinality(Tran(x))][x] : x \in R(m)})
<1> DEFINE M == Cardinality(Tran(m))
<1>fin. IsFiniteSet(Tran(m)) /\ M \in Nat  BY TranCardNat
<1>mm. m \in MessagesWithTranSizeAtMost(M)
  <2>1. Cardinality(Tran(m)) \in Nat  BY TranCardNat
  <2>2. Cardinality(Tran(m)) <= M  BY <2>1, <1>fin, SMT
  <2> QED BY <2>2 DEF MessagesWithTranSizeAtMost
<1>nz. M # 0
  <2>1. m \in Tran(m)  BY DEF Tran
  <2> QED BY <1>fin, <2>1, FS_EmptySet
<1>step. GFunMI(F, R)[M][m]
           = F(m, IF M = 0 THEN {} ELSE {GFunMI(F, R)[M-1][y] : y \in R(m)})
  BY <1>fin, <1>mm, gStepMI
<1>unfold. GFunMI(F, R)[M][m] = F(m, {GFunMI(F, R)[M-1][y] : y \in R(m)})
  BY <1>step, <1>nz
<1>eq. {GFunMI(F, R)[M-1][y] : y \in R(m)}
       = {GFunMI(F, R)[Cardinality(Tran(x))][x] : x \in R(m)}
  <2>0. M - 1 \in Nat  BY <1>fin, <1>nz, SMT
  <2>1. ASSUME NEW y \in R(m)
        PROVE GFunMI(F, R)[M-1][y] = GFunMI(F, R)[Cardinality(Tran(y))][y]
    <3>1. y \in Messages  OBVIOUS
    <3>2. Cardinality(Tran(y)) < M  OBVIOUS
    <3>3. Cardinality(Tran(y)) \in Nat  BY <3>1, TranCardNat
    <3>4. Cardinality(Tran(y)) <= M-1  BY <3>2, <3>3, <2>0, <1>fin, SMT
    <3>5. y \in MessagesWithTranSizeAtMost(M-1)  BY <3>1, <3>4 DEF MessagesWithTranSizeAtMost
    <3> QED BY <2>0, <3>5, LevelIndepGFunMI
  <2> QED BY <2>1
<1> QED BY <1>unfold, <1>eq

\* Bridges: the file's RecursiveMessage*Func equal GFunMI at the message's level.
LEMMA RMTFViaG ==
  ASSUME NEW F(_,_), NEW z
  PROVE RecursiveMessageTranFunc(F, z) = GFunMI(F, TranExclusive)[Cardinality(Tran(z))][z]
BY DEF RecursiveMessageTranFunc, GFunMI

LEMMA RMRFViaG ==
  ASSUME NEW F(_,_), NEW z
  PROVE RecursiveMessageRefsFunc(F, z) = GFunMI(F, Refs)[Cardinality(Tran(z))][z]
BY DEF RecursiveMessageRefsFunc, GFunMI

LEMMA RecursiveMessageTranFuncRec ==
    ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
           NEW m \in Messages,
           NEW F(_,_)
    PROVE RecursiveMessageTranFunc(F, m) =
          F(m, {RecursiveMessageTranFunc(F, x) : x \in TranExclusive(m)})
<1>h1. \A x \in Messages : TranExclusive(x) \subseteq Messages
  BY TranSubMessages DEF TranExclusive
<1>h2. \A x \in Messages : \A y \in TranExclusive(x) :
         Cardinality(Tran(y)) < Cardinality(Tran(x))
  BY TranExclusiveDecreasesTranSize
<1>1. GFunMI(F, TranExclusive)[Cardinality(Tran(m))][m]
        = F(m, {GFunMI(F, TranExclusive)[Cardinality(Tran(x))][x] : x \in TranExclusive(m)})
  BY <1>h1, <1>h2, GFunRecMI
<1>2. RecursiveMessageTranFunc(F, m) = GFunMI(F, TranExclusive)[Cardinality(Tran(m))][m]
  BY RMTFViaG
<1>3. {GFunMI(F, TranExclusive)[Cardinality(Tran(x))][x] : x \in TranExclusive(m)}
      = {RecursiveMessageTranFunc(F, x) : x \in TranExclusive(m)}
  BY RMTFViaG
<1> QED BY <1>1, <1>2, <1>3

LEMMA RecursiveMessageRefsFuncRec ==
    ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
           NEW m \in Messages,
           NEW F(_,_)
    PROVE RecursiveMessageRefsFunc(F, m) =
          F(m, {RecursiveMessageRefsFunc(F, x) : x \in Refs(m)})
<1>sub. \A x \in Messages : Refs(x) \subseteq TranExclusive(x)
  BY DEF Refs
<1>h1. \A x \in Messages : Refs(x) \subseteq Messages
  BY <1>sub, TranSubMessages DEF TranExclusive
<1>h2. \A x \in Messages : \A y \in Refs(x) :
         Cardinality(Tran(y)) < Cardinality(Tran(x))
  BY <1>sub, TranExclusiveDecreasesTranSize
<1>1. GFunMI(F, Refs)[Cardinality(Tran(m))][m]
        = F(m, {GFunMI(F, Refs)[Cardinality(Tran(x))][x] : x \in Refs(m)})
  BY <1>h1, <1>h2, GFunRecMI
<1>2. RecursiveMessageRefsFunc(F, m) = GFunMI(F, Refs)[Cardinality(Tran(m))][m]
  BY RMRFViaG
<1>3. {GFunMI(F, Refs)[Cardinality(Tran(x))][x] : x \in Refs(m)}
      = {RecursiveMessageRefsFunc(F, x) : x \in Refs(m)}
  BY RMRFViaG
<1> QED BY <1>1, <1>2, <1>3

\* might be easier to prove by defining using  RecursiveMessageRefsFunc, and using proofs from there.
\* A named operator for the Tran-size, so FiniteMaxExists can be applied to it
\* (TLAPS can instantiate the operator argument f with a named operator, but not
\* with the anonymous lambda y |-> Cardinality(Tran(y))).
TranCard(mm) == Cardinality(Tran(mm))

\* A finite, non-empty set of messages has an element of maximal Tran-size.
\* (First-order wrapper around FiniteMaxExists, so it can be applied to a set
\* given by a local definition.)
LEMMA TranMaxExists ==
    ASSUME TranFinite,
           NEW T, IsFiniteSet(T), T # {}, T \subseteq Messages
    PROVE \E r \in T : \A y \in T : Cardinality(Tran(y)) <= Cardinality(Tran(r))
<1>1. \A x \in T : TranCard(x) \in Nat
  <2>1. ASSUME NEW x \in T PROVE TranCard(x) \in Nat
    <3>1. x \in Messages  BY <2>1
    <3> QED BY <3>1, TranCardNat DEF TranCard
  <2> QED BY <2>1
<1>2. \E r \in T : \A y \in T : TranCard(y) <= TranCard(r)
  BY <1>1, FiniteMaxExists
<1> QED BY <1>2 DEF TranCard

LEMMA TranRefs ==
    ASSUME TypeOKMessageInterface, TranFinite, TranTrans, TranAcyclic,
           NEW m \in Messages
    PROVE Tran(m) = {m} \cup UNION {Tran(r) : r \in Refs(m)}
<1>fin. IsFiniteSet(Tran(m))  BY DEF TranFinite
<1>subM. Tran(m) \subseteq Messages  BY TranSubMessages
\* (superset) RHS \subseteq Tran(m)
<1>sup. {m} \cup UNION {Tran(r) : r \in Refs(m)} \subseteq Tran(m)
  <2>1. m \in Tran(m)  BY DEF Tran
  <2>2. ASSUME NEW r \in Refs(m) PROVE Tran(r) \subseteq Tran(m)
    <3>1. r \in TranExclusive(m)  BY <2>2 DEF Refs
    <3>2. r \in Tran(m)  BY <3>1 DEF TranExclusive
    <3> QED BY <3>2 DEF TranTrans
  <2> QED BY <2>1, <2>2
\* (subset) Tran(m) \subseteq RHS
<1>sub. Tran(m) \subseteq {m} \cup UNION {Tran(r) : r \in Refs(m)}
  <2> SUFFICES ASSUME NEW z \in Tran(m), z # m
               PROVE  z \in UNION {Tran(r) : r \in Refs(m)}
    OBVIOUS
  <2>z. z \in TranExclusive(m)  BY DEF TranExclusive
  <2> DEFINE Sz == {y \in TranExclusive(m) : z \in Tran(y)}
  <2>ztran. z \in Tran(z)  BY DEF Tran
  <2>zin. z \in Sz  BY <2>z, <2>ztran
  <2>TEsubM. TranExclusive(m) \subseteq Messages  BY <1>subM DEF TranExclusive
  <2>finSz. IsFiniteSet(Sz)
    <3>1. TranExclusive(m) \subseteq Tran(m)  BY DEF TranExclusive
    <3>2. Sz \subseteq Tran(m)  BY <3>1
    <3> QED BY <3>2, <1>fin, FS_Subset
  <2>SzM. Sz \subseteq Messages  BY <2>TEsubM
  <2>max. PICK r \in Sz : \A y \in Sz : Cardinality(Tran(y)) <= Cardinality(Tran(r))
    BY <2>finSz, <2>zin, <2>SzM, TranMaxExists
  <2>rTE. r \in TranExclusive(m)  BY <2>max
  <2>rz. z \in Tran(r)  BY <2>max
  <2>rRefs. r \in Refs(m)
    <3> SUFFICES ASSUME NEW y \in TranExclusive(m), r \in TranExclusive(y)
                 PROVE FALSE
      BY <2>rTE DEF Refs
    <3>yM. y \in Messages  BY <2>TEsubM
    <3>1. r \in Tran(y)  BY DEF TranExclusive
    <3>2. Tran(r) \subseteq Tran(y)  BY <3>yM, <3>1 DEF TranTrans
    <3>3. z \in Tran(y)  BY <2>rz, <3>2
    <3>4. y \in Sz  BY <3>3
    <3>5. Cardinality(Tran(y)) <= Cardinality(Tran(r))  BY <3>4, <2>max
    <3>6. Cardinality(Tran(r)) < Cardinality(Tran(y))  BY <3>yM, TranExclusiveDecreasesTranSize
    <3>7. Cardinality(Tran(y)) \in Nat /\ Cardinality(Tran(r)) \in Nat
      BY <3>yM, <2>rTE, <2>TEsubM, TranCardNat
    <3> QED BY <3>5, <3>6, <3>7, SMT
  <2> QED BY <2>rRefs, <2>rz
<1> QED BY <1>sup, <1>sub

\* ===================================================================
\* Uniqueness of the fixpoints: any two solutions of each recursion agree
\* on Messages.  Both reduce, via GFunLeastMI, to equality with the
\* canonical GFunMI solution.
\* ===================================================================

\* Any solution H of the recursion equals the canonical GFunMI solution,
\* by course-of-values induction on the Cardinality(Tran(.)) measure.
LEMMA GFunLeastMI ==
  ASSUME TranFinite, NEW F(_,_), NEW R(_), NEW H(_),
         \A x \in Messages : R(x) \subseteq Messages,
         \A x \in Messages : \A y \in R(x) :
             Cardinality(Tran(y)) < Cardinality(Tran(x)),
         \A mm \in Messages : H(mm) = F(mm, {H(p) : p \in R(mm)})
  PROVE \A mm \in Messages : H(mm) = GFunMI(F, R)[Cardinality(Tran(mm))][mm]
<1> DEFINE lev(z) == Cardinality(Tran(z))
<1> DEFINE Q(n) == \A mm \in Messages : lev(mm) = n =>
                     H(mm) = GFunMI(F, R)[lev(mm)][mm]
<1> SUFFICES \A n \in Nat : Q(n)  BY TranCardNat DEF Q
<1> HIDE DEF Q
<1>ind. \A n \in Nat : (\A kk \in 0..(n-1) : Q(kk)) => Q(n)
  <2> USE DEF Q
  <2> SUFFICES ASSUME NEW n \in Nat, \A kk \in 0..(n-1) : Q(kk),
                      NEW mm \in Messages, lev(mm) = n
               PROVE  H(mm) = GFunMI(F, R)[lev(mm)][mm]
    OBVIOUS
  <2>1. H(mm) = F(mm, {H(p) : p \in R(mm)})  OBVIOUS
  <2>2. GFunMI(F, R)[lev(mm)][mm] = F(mm, {GFunMI(F, R)[lev(p)][p] : p \in R(mm)})
    BY GFunRecMI
  <2>3. {H(p) : p \in R(mm)} = {GFunMI(F, R)[lev(p)][p] : p \in R(mm)}
    <3>1. ASSUME NEW p \in R(mm) PROVE H(p) = GFunMI(F, R)[lev(p)][p]
      <4>1. p \in Messages  OBVIOUS
      <4>2. lev(p) < lev(mm)  OBVIOUS
      <4>3. lev(p) \in Nat  BY <4>1, TranCardNat
      <4>4. lev(p) \in 0..(n-1)  BY <4>2, <4>3, SMT
      <4> QED BY <4>1, <4>4
    <3> QED BY <3>1
  <2> QED BY <2>1, <2>2, <2>3
<1> QED BY <1>ind, GeneralNatInduction, IsaM("blast")

LEMMA RecursiveMessageTranFuncUnique ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic, NEW F(_,_), NEW H1(_), NEW H2(_),
         \A mm \in Messages : H1(mm) = F(mm, {H1(p) : p \in TranExclusive(mm)}),
         \A mm \in Messages : H2(mm) = F(mm, {H2(p) : p \in TranExclusive(mm)})
  PROVE \A mm \in Messages : H1(mm) = H2(mm)
<1>h1. \A x \in Messages : TranExclusive(x) \subseteq Messages
  BY TranSubMessages DEF TranExclusive
<1>h2. \A x \in Messages : \A y \in TranExclusive(x) :
         Cardinality(Tran(y)) < Cardinality(Tran(x))
  BY TranExclusiveDecreasesTranSize
<1>1. \A mm \in Messages : H1(mm) = GFunMI(F, TranExclusive)[Cardinality(Tran(mm))][mm]
  BY <1>h1, <1>h2, GFunLeastMI
<1>2. \A mm \in Messages : H2(mm) = GFunMI(F, TranExclusive)[Cardinality(Tran(mm))][mm]
  BY <1>h1, <1>h2, GFunLeastMI
<1> QED BY <1>1, <1>2

LEMMA RecursiveMessageRefsFuncUnique ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic, NEW F(_,_), NEW H1(_), NEW H2(_),
         \A mm \in Messages : H1(mm) = F(mm, {H1(p) : p \in Refs(mm)}),
         \A mm \in Messages : H2(mm) = F(mm, {H2(p) : p \in Refs(mm)})
  PROVE \A mm \in Messages : H1(mm) = H2(mm)
<1>sub. \A x \in Messages : Refs(x) \subseteq TranExclusive(x)
  BY DEF Refs
<1>h1. \A x \in Messages : Refs(x) \subseteq Messages
  BY <1>sub, TranSubMessages DEF TranExclusive
<1>h2. \A x \in Messages : \A y \in Refs(x) :
         Cardinality(Tran(y)) < Cardinality(Tran(x))
  BY <1>sub, TranExclusiveDecreasesTranSize
<1>1. \A mm \in Messages : H1(mm) = GFunMI(F, Refs)[Cardinality(Tran(mm))][mm]
  BY <1>h1, <1>h2, GFunLeastMI
<1>2. \A mm \in Messages : H2(mm) = GFunMI(F, Refs)[Cardinality(Tran(mm))][mm]
  BY <1>h1, <1>h2, GFunLeastMI
<1> QED BY <1>1, <1>2

\* Well-founded induction along Refs.  Course-of-values on Cardinality(Tran(.))
\* (this file's level measure): a message x's refs have strictly smaller Tran
\* (TranExclusiveDecreasesTranSize, via Refs(x) \subseteq TranExclusive(x)) and
\* stay within Messages (TranSubMessages), so each ref satisfies H by the IH;
\* the hypothesis then lifts that to H(x). Mirrors HPaxos.tla's RefsInduction.
LEMMA RefsInduction ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         NEW m \in Messages,
         NEW H(_),
         \A x \in Messages: (\A y \in Refs(x) : H(y)) => H(x)
  PROVE H(m)
<1> DEFINE lev(z) == Cardinality(Tran(z))
<1> DEFINE Q(n) == \A x \in Messages : lev(x) = n => H(x)
<1> SUFFICES \A n \in Nat : Q(n)  BY TranCardNat DEF Q
<1> HIDE DEF Q
<1>ind. \A n \in Nat : (\A kk \in 0..(n-1) : Q(kk)) => Q(n)
  <2> USE DEF Q
  <2> SUFFICES ASSUME NEW n \in Nat, \A kk \in 0..(n-1) : Q(kk),
                      NEW x \in Messages, lev(x) = n
               PROVE  H(x)
    OBVIOUS
  <2>sub. Refs(x) \subseteq TranExclusive(x)  BY DEF Refs
  <2>tc. Refs(x) \subseteq Messages  BY <2>sub, TranSubMessages DEF TranExclusive
  <2>r. \A y \in Refs(x) : H(y)
    <3> SUFFICES ASSUME NEW y \in Refs(x) PROVE H(y)  OBVIOUS
    <3>3. y \in Messages  BY <2>tc
    <3>5. lev(y) < lev(x)  BY <2>sub, TranExclusiveDecreasesTranSize
    <3>6. lev(y) \in Nat  BY <3>3, TranCardNat
    <3>7. lev(y) \in 0..(n-1)  BY <3>5, <3>6
    <3> QED BY <3>3, <3>7
  <2> QED BY <2>r
<1> QED BY <1>ind, GeneralNatInduction, IsaM("blast")


LEMMA AlwaysAMaxProposal ==
  ( /\ AlwaysAProposal
    /\ TranFinite
    /\ TypeOKMessageInterface
  ) => \A m \in Messages : MaxProposals(m) # {}
<1> SUFFICES ASSUME AlwaysAProposal, TranFinite, TypeOKMessageInterface,
                    NEW m \in Messages
             PROVE MaxProposals(m) # {}
  OBVIOUS
<1>ne. GetProposals(m) # {}  BY DEF AlwaysAProposal
<1>fin. IsFiniteSet(GetProposals(m))
  <2>1. GetProposals(m) \subseteq Tran(m)  BY DEF GetProposals
  <2>2. IsFiniteSet(Tran(m))  BY DEF TranFinite
  <2> QED BY <2>1, <2>2, FS_Subset
<1>bal. \A x \in GetProposals(m) : ProposalBal(x) \in Nat
  <2>1. ASSUME NEW x \in GetProposals(m) PROVE ProposalBal(x) \in Nat
    <3>1. x \in Proposals  BY <2>1 DEF GetProposals
    <3>2. MessageInterface.proposalbal \in [Proposals -> Ballots]
      BY DEF TypeOKMessageInterface
    <3> QED BY <3>1, <3>2 DEF ProposalBal, Ballots
  <2> QED BY <2>1
<1>max. \E r \in GetProposals(m) : \A y \in GetProposals(m) : ProposalBal(y) <= ProposalBal(r)
  BY <1>fin, <1>ne, <1>bal, FiniteMaxExists
<1>r. PICK r \in GetProposals(m) : \A y \in GetProposals(m) : ProposalBal(y) <= ProposalBal(r)
  BY <1>max
<1>rNat. ProposalBal(r) \in Nat  BY <1>r, <1>bal
<1>rInT. ProposalBal(r) \in {ProposalBal(x) : x \in GetProposals(m)}
  BY <1>r
<1>rUB. \A y \in {ProposalBal(x) : x \in GetProposals(m)} : y <= ProposalBal(r)
  <2>1. ASSUME NEW y \in {ProposalBal(x) : x \in GetProposals(m)}
        PROVE y <= ProposalBal(r)
    <3>1. PICK x \in GetProposals(m) : y = ProposalBal(x)  BY <2>1
    <3> QED BY <3>1, <1>r
  <2> QED BY <2>1
<1>witness. \E x \in {ProposalBal(x) : x \in GetProposals(m)} :
              \A y \in {ProposalBal(x) : x \in GetProposals(m)} : x >= y
  BY <1>rInT, <1>rUB
<1>choose. /\ Max({ProposalBal(x) : x \in GetProposals(m)})
              \in {ProposalBal(x) : x \in GetProposals(m)}
           /\ \A y \in {ProposalBal(x) : x \in GetProposals(m)} :
                Max({ProposalBal(x) : x \in GetProposals(m)}) >= y
  BY <1>witness DEF Max
<1>Bmr. B(m) = ProposalBal(r)
  <2>le1. B(m) >= ProposalBal(r)  BY <1>choose, <1>rInT DEF B
  <2>le2. ProposalBal(r) >= B(m)  BY <1>choose, <1>rUB DEF B
  <2>BinSet. B(m) \in {ProposalBal(x) : x \in GetProposals(m)}  BY <1>choose DEF B
  <2>BNat. B(m) \in Nat
    <3>1. PICK x \in GetProposals(m) : B(m) = ProposalBal(x)  BY <2>BinSet
    <3> QED BY <3>1, <1>bal
  <2> QED BY <2>le1, <2>le2, <2>BNat, <1>rNat
<1>rMax. r \in MaxProposals(m)
  BY <1>r, <1>Bmr DEF MaxProposals
<1> QED BY <1>rMax

\* Max({ProposalBal(x) : x \in T}), for any finite nonempty T \subseteq Proposals,
\* is itself a member of that set and an upper bound for it.
LEMMA MaxBSetProperty ==
    ASSUME TypeOKMessageInterface,
           NEW T, IsFiniteSet(T), T # {}, T \subseteq Proposals
    PROVE /\ Max({ProposalBal(x) : x \in T}) \in {ProposalBal(x) : x \in T}
          /\ \A y \in {ProposalBal(x) : x \in T} : Max({ProposalBal(x) : x \in T}) >= y
<1>bal. \A x \in T : ProposalBal(x) \in Nat
  <2>1. ASSUME NEW x \in T PROVE ProposalBal(x) \in Nat
    <3>1. MessageInterface.proposalbal \in [Proposals -> Ballots]
      BY DEF TypeOKMessageInterface
    <3> QED BY <2>1, <3>1 DEF ProposalBal, Ballots
  <2> QED BY <2>1
<1>max. \E r \in T : \A y \in T : ProposalBal(y) <= ProposalBal(r)
  BY <1>bal, FiniteMaxExists
<1>r. PICK r \in T : \A y \in T : ProposalBal(y) <= ProposalBal(r)  BY <1>max
<1>rInT. ProposalBal(r) \in {ProposalBal(x) : x \in T}  BY <1>r
<1>rUB. \A y \in {ProposalBal(x) : x \in T} : y <= ProposalBal(r)
  <2>1. ASSUME NEW y \in {ProposalBal(x) : x \in T} PROVE y <= ProposalBal(r)
    <3>1. PICK x \in T : y = ProposalBal(x)  BY <2>1
    <3> QED BY <3>1, <1>r
  <2> QED BY <2>1
<1>witness. \E x \in {ProposalBal(x) : x \in T} : \A y \in {ProposalBal(x) : x \in T} : x >= y
  BY <1>rInT, <1>rUB
<1> QED BY <1>witness DEF Max

\* B(m) is always a valid ballot. Needs AlwaysAProposal to guarantee
\* GetProposals(m) # {}, so Max({ProposalBal(x) : x \in GetProposals(m)}) is
\* well-defined.
LEMMA BBallot ==
  ASSUME AlwaysAProposal, TranFinite, TypeOKMessageInterface, NEW m \in Messages
  PROVE B(m) \in Ballots
<1>ne. GetProposals(m) # {}  BY DEF AlwaysAProposal
<1>fin. IsFiniteSet(GetProposals(m))
  <2>1. GetProposals(m) \subseteq Tran(m)  BY DEF GetProposals
  <2>2. IsFiniteSet(Tran(m))  BY DEF TranFinite
  <2> QED BY <2>1, <2>2, FS_Subset
<1>sub. GetProposals(m) \subseteq Proposals  BY DEF GetProposals
<1>typeOK. TypeOKMessageInterface  OBVIOUS
<1>mbp. /\ Max({ProposalBal(x) : x \in GetProposals(m)}) \in {ProposalBal(x) : x \in GetProposals(m)}
        /\ \A y \in {ProposalBal(x) : x \in GetProposals(m)} :
             Max({ProposalBal(x) : x \in GetProposals(m)}) >= y
  BY <1>fin, <1>ne, <1>sub, <1>typeOK, MaxBSetProperty
<1>1. B(m) \in {ProposalBal(x) : x \in GetProposals(m)}  BY <1>mbp DEF B
<1>2. \A x \in GetProposals(m) : ProposalBal(x) \in Ballots
  <2>1. ASSUME NEW x \in GetProposals(m) PROVE ProposalBal(x) \in Ballots
    <3>1. x \in Proposals  BY <2>1 DEF GetProposals
    <3>2. MessageInterface.proposalbal \in [Proposals -> Ballots]
      BY DEF TypeOKMessageInterface
    <3> QED BY <3>1, <3>2 DEF ProposalBal
  <2> QED BY <2>1
<1>3. PICK x \in GetProposals(m) : B(m) = ProposalBal(x)  BY <1>1
<1> QED BY <1>3, <1>2

\* B is recursively characterized by Refs: B(m) is monotone along Tran(m), and
\* is either m's own ballot (if m is a proposal achieving the max) or equals
\* B(r) for some direct ref r (if the max-achieving proposal lies further
\* down). Direct (non-inductive) argument: GetProposals(m) decomposes along
\* Refs(m) via TranRefs, so the max-achieving proposal is either m itself or
\* lies within some ref's own GetProposals -- in which case that ref's own B
\* (by the monotonicity half, applied to that ref) is sandwiched between the
\* achieving ballot and B(m), forcing equality.
LEMMA BRec ==
  ASSUME TypeOKMessageInterface, TranFinite, TranTrans, TranAcyclic, AlwaysAProposal,
         NEW m \in Messages
  PROVE /\ \A t \in Tran(m) : B(t) <= B(m)
        /\ (\/ m \in Proposals /\ B(m) = ProposalBal(m)
            \/ \E r \in Refs(m) : B(m) = B(r))
<1>finM. IsFiniteSet(GetProposals(m))
  <2>1. GetProposals(m) \subseteq Tran(m)  BY DEF GetProposals
  <2>2. IsFiniteSet(Tran(m))  BY DEF TranFinite
  <2> QED BY <2>1, <2>2, FS_Subset
<1>subM. GetProposals(m) \subseteq Proposals  BY DEF GetProposals
<1>neM. GetProposals(m) # {}  BY DEF AlwaysAProposal
<1>typeOK. TypeOKMessageInterface  OBVIOUS
<1>Mchoose. /\ B(m) \in {ProposalBal(x) : x \in GetProposals(m)}
            /\ \A y \in {ProposalBal(x) : x \in GetProposals(m)} : B(m) >= y
  BY <1>finM, <1>subM, <1>neM, <1>typeOK, MaxBSetProperty DEF B

<1>mono. \A t \in Tran(m) : B(t) <= B(m)
  <2> SUFFICES ASSUME NEW t \in Tran(m) PROVE B(t) <= B(m)  OBVIOUS
  <2>tMsg. t \in Messages  BY TranSubMessages
  <2>subT. Tran(t) \subseteq Tran(m)  BY <2>tMsg DEF TranTrans
  <2>subGP. GetProposals(t) \subseteq GetProposals(m)  BY <2>subT DEF GetProposals
  <2>finT. IsFiniteSet(GetProposals(t))
    <3>1. GetProposals(t) \subseteq Tran(t)  BY DEF GetProposals
    <3>2. IsFiniteSet(Tran(t))  BY <2>tMsg DEF TranFinite
    <3> QED BY <3>1, <3>2, FS_Subset
  <2>subPT. GetProposals(t) \subseteq Proposals  BY DEF GetProposals
  <2>neT. GetProposals(t) # {}  BY <2>tMsg DEF AlwaysAProposal
  <2>Tchoose. /\ B(t) \in {ProposalBal(x) : x \in GetProposals(t)}
              /\ \A y \in {ProposalBal(x) : x \in GetProposals(t)} : B(t) >= y
    BY <2>finT, <2>subPT, <2>neT, <1>typeOK, MaxBSetProperty DEF B
  <2>1. B(t) \in {ProposalBal(x) : x \in GetProposals(m)}
    <3>1. PICK x \in GetProposals(t) : B(t) = ProposalBal(x)  BY <2>Tchoose
    <3>2. x \in GetProposals(m)  BY <3>1, <2>subGP
    <3> QED BY <3>1, <3>2
  <2> QED BY <2>1, <1>Mchoose

<1>disj. \/ m \in Proposals /\ B(m) = ProposalBal(m)
         \/ \E r \in Refs(m) : B(m) = B(r)
  <2>x0. PICK x0 \in GetProposals(m) : B(m) = ProposalBal(x0)  BY <1>Mchoose
  <2>decomp. Tran(m) = {m} \cup UNION {Tran(r) : r \in Refs(m)}  BY TranRefs
  <2>x0in. x0 \in {m} \cup UNION {Tran(r) : r \in Refs(m)}
    <3>1. x0 \in Tran(m)  BY <2>x0 DEF GetProposals
    <3> QED BY <3>1, <2>decomp
  <2>case. CASE x0 = m
    <3>1. m \in Proposals  BY <2>x0, <2>case DEF GetProposals
    <3> QED BY <3>1, <2>x0, <2>case
  <2>case2. CASE x0 # m
    <3>1. x0 \in UNION {Tran(r) : r \in Refs(m)}  BY <2>x0in, <2>case2
    <3>2. PICK r \in Refs(m) : x0 \in Tran(r)  BY <3>1
    <3>3. x0 \in Proposals  BY <2>x0 DEF GetProposals
    <3>4. x0 \in GetProposals(r)  BY <3>2, <3>3 DEF GetProposals
    <3>rIn. r \in Tran(m)
      <4>1. r \in TranExclusive(m)  BY <3>2 DEF Refs
      <4> QED BY <4>1 DEF TranExclusive
    <3>rBnd. B(r) <= B(m)  BY <1>mono, <3>rIn
    <3>rMsg. r \in Messages  BY <3>rIn, TranSubMessages
    <3>finR. IsFiniteSet(GetProposals(r))
      <4>1. GetProposals(r) \subseteq Tran(r)  BY DEF GetProposals
      <4>2. IsFiniteSet(Tran(r))  BY <3>rMsg DEF TranFinite
      <4> QED BY <4>1, <4>2, FS_Subset
    <3>subPR. GetProposals(r) \subseteq Proposals  BY DEF GetProposals
    <3>neR. GetProposals(r) # {}  BY <3>rMsg DEF AlwaysAProposal
    <3>Rchoose. /\ B(r) \in {ProposalBal(x) : x \in GetProposals(r)}
                /\ \A y \in {ProposalBal(x) : x \in GetProposals(r)} : B(r) >= y
      BY <3>finR, <3>subPR, <3>neR, <1>typeOK, MaxBSetProperty DEF B
    <3>ub. B(r) >= ProposalBal(x0)  BY <3>Rchoose, <3>4
    <3>x0Nat. ProposalBal(x0) \in Nat
      <4>1. x0 \in Proposals  BY <2>x0 DEF GetProposals
      <4>2. MessageInterface.proposalbal \in [Proposals -> Ballots]
        BY DEF TypeOKMessageInterface
      <4> QED BY <4>1, <4>2 DEF ProposalBal, Ballots
    <3>rNat. B(r) \in Nat
      <4>1. PICK y \in GetProposals(r) : B(r) = ProposalBal(y)  BY <3>Rchoose
      <4>2. y \in Proposals  BY <4>1 DEF GetProposals
      <4>3. MessageInterface.proposalbal \in [Proposals -> Ballots]
        BY DEF TypeOKMessageInterface
      <4> QED BY <4>1, <4>2, <4>3 DEF ProposalBal, Ballots
    <3>eq. B(m) = B(r)  BY <2>x0, <3>ub, <3>rBnd, <3>x0Nat, <3>rNat, SMT
    <3> QED BY <3>eq, <3>2
  <2> QED BY <2>case, <2>case2
<1> QED BY <1>mono, <1>disj

LEMMA MaxProposalB ==
  ( /\ TranFinite
    /\ TranTrans
    /\ TypeOKMessageInterface
  ) => \A m \in Messages : \A p \in MaxProposals(m) : B(m) = B(p)
<1> SUFFICES ASSUME TranFinite, TranTrans, TypeOKMessageInterface,
                    NEW m \in Messages, NEW p \in MaxProposals(m)
             PROVE B(m) = B(p)
  OBVIOUS
<1>pIn. p \in GetProposals(m) /\ ProposalBal(p) = B(m)  BY DEF MaxProposals
<1>pProp. p \in Proposals  BY <1>pIn DEF GetProposals
<1>pMsg. p \in Messages  BY <1>pProp DEF TypeOKMessageInterface
<1>pSelf. p \in GetProposals(p)
  <2>1. p \in Tran(p)  BY DEF Tran
  <2> QED BY <2>1, <1>pProp DEF GetProposals
<1>sub. GetProposals(p) \subseteq GetProposals(m)
  <2>1. p \in Tran(m)  BY <1>pIn DEF GetProposals
  <2>2. Tran(p) \subseteq Tran(m)  BY <2>1, <1>pMsg DEF TranTrans
  <2> QED BY <2>2 DEF GetProposals
<1>finP. IsFiniteSet(GetProposals(p))
  <2>1. GetProposals(p) \subseteq Tran(p)  BY DEF GetProposals
  <2>2. IsFiniteSet(Tran(p))  BY <1>pMsg DEF TranFinite
  <2> QED BY <2>1, <2>2, FS_Subset
<1>finM. IsFiniteSet(GetProposals(m))
  <2>1. GetProposals(m) \subseteq Tran(m)  BY DEF GetProposals
  <2>2. IsFiniteSet(Tran(m))  BY DEF TranFinite
  <2> QED BY <2>1, <2>2, FS_Subset
<1>subPP. GetProposals(p) \subseteq Proposals  BY DEF GetProposals
<1>subPM. GetProposals(m) \subseteq Proposals  BY DEF GetProposals
<1>pNE. GetProposals(p) # {}  BY <1>pSelf
<1>mNE. GetProposals(m) # {}  BY <1>pIn
<1>Pchoose. /\ B(p) \in {ProposalBal(x) : x \in GetProposals(p)}
            /\ \A y \in {ProposalBal(x) : x \in GetProposals(p)} : B(p) >= y
  BY <1>finP, <1>subPP, <1>pNE, MaxBSetProperty DEF B
<1>Mchoose. /\ B(m) \in {ProposalBal(x) : x \in GetProposals(m)}
            /\ \A y \in {ProposalBal(x) : x \in GetProposals(m)} : B(m) >= y
  BY <1>finM, <1>subPM, <1>mNE, MaxBSetProperty DEF B
<1>ge. B(p) >= B(m)
  <2>1. ProposalBal(p) \in {ProposalBal(x) : x \in GetProposals(p)}
    BY <1>pSelf
  <2> QED BY <2>1, <1>Pchoose, <1>pIn
<1>le. B(m) >= B(p)
  <2>1. B(p) \in {ProposalBal(x) : x \in GetProposals(m)}
    BY <1>Pchoose, <1>sub
  <2> QED BY <2>1, <1>Mchoose
<1>balP. \A x \in GetProposals(p) : ProposalBal(x) \in Nat
  <2>1. ASSUME NEW x \in GetProposals(p) PROVE ProposalBal(x) \in Nat
    <3>1. x \in Proposals  BY <2>1 DEF GetProposals
    <3>2. MessageInterface.proposalbal \in [Proposals -> Ballots]
      BY DEF TypeOKMessageInterface
    <3> QED BY <3>1, <3>2 DEF ProposalBal, Ballots
  <2> QED BY <2>1
<1>balM. \A x \in GetProposals(m) : ProposalBal(x) \in Nat
  <2>1. ASSUME NEW x \in GetProposals(m) PROVE ProposalBal(x) \in Nat
    <3>1. x \in Proposals  BY <2>1 DEF GetProposals
    <3>2. MessageInterface.proposalbal \in [Proposals -> Ballots]
      BY DEF TypeOKMessageInterface
    <3> QED BY <3>1, <3>2 DEF ProposalBal, Ballots
  <2> QED BY <2>1
<1>Nats. B(p) \in Nat /\ B(m) \in Nat
  <2>1. {ProposalBal(x) : x \in GetProposals(p)} \subseteq Nat  BY <1>balP
  <2>2. {ProposalBal(x) : x \in GetProposals(m)} \subseteq Nat  BY <1>balM
  <2> QED BY <2>1, <2>2, <1>Pchoose, <1>Mchoose
<1> QED BY <1>ge, <1>le, <1>Nats

\* CombinedFreshQdLrnsId satisfies its defining recursion, and its id field is
\* the argument (mirrors HPaxos.tla's CflRec/CflId).
LEMMA CombinedFreshQdLrnsIdRec ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic, NEW x \in Messages
  PROVE CombinedFreshQdLrnsId(x)
          = CombinedFreshQdLrnsIdR(x, {CombinedFreshQdLrnsId(p) : p \in TranExclusive(x)})
<1>1. RecursiveMessageTranFunc(CombinedFreshQdLrnsIdR, x)
        = CombinedFreshQdLrnsIdR(x,
            {RecursiveMessageTranFunc(CombinedFreshQdLrnsIdR, p) : p \in TranExclusive(x)})
  BY RecursiveMessageTranFuncRec
<1> QED BY <1>1 DEF CombinedFreshQdLrnsId

\* CombinedFreshQdLrnsId is the UNIQUE solution of its recursion. Unlike
\* HPaxos.tla's CombinedFreshQdLrnsIdUnique (which redoes the domain-closure /
\* level-decrease argument via RecursiveMessageFuncLeast), this file already has
\* RecursiveMessageTranFuncUnique -- "any two solutions of the same recursion
\* agree" -- specialized to F := CombinedFreshQdLrnsIdR with H1 := H (assumed)
\* and H2 := CombinedFreshQdLrnsId (shown to satisfy the same equation by
\* CombinedFreshQdLrnsIdRec).
LEMMA CombinedFreshQdLrnsIdUnique ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic, NEW H(_),
         \A x \in Messages :
            H(x) = CombinedFreshQdLrnsIdR(x, {H(p) : p \in TranExclusive(x)})
  PROVE \A x \in Messages : H(x) = CombinedFreshQdLrnsId(x)
<1> DEFINE lev(z) == Cardinality(Tran(z))
<1> DEFINE Q(n) == \A mm \in Messages : lev(mm) = n =>
                     H(mm) = CombinedFreshQdLrnsId(mm)
<1> SUFFICES \A n \in Nat : Q(n)  BY TranCardNat DEF Q
<1> HIDE DEF Q
<1>ind. \A n \in Nat : (\A kk \in 0..(n-1) : Q(kk)) => Q(n)
  <2> USE DEF Q
  <2> SUFFICES ASSUME NEW n \in Nat, \A kk \in 0..(n-1) : Q(kk),
                      NEW mm \in Messages, lev(mm) = n
               PROVE  H(mm) = CombinedFreshQdLrnsId(mm)
    OBVIOUS
  <2>1. H(mm) = CombinedFreshQdLrnsIdR(mm, {H(p) : p \in TranExclusive(mm)})  OBVIOUS
  <2>2. CombinedFreshQdLrnsId(mm)
          = CombinedFreshQdLrnsIdR(mm, {CombinedFreshQdLrnsId(p) : p \in TranExclusive(mm)})
    BY CombinedFreshQdLrnsIdRec
  <2>3. {H(p) : p \in TranExclusive(mm)} = {CombinedFreshQdLrnsId(p) : p \in TranExclusive(mm)}
    <3>1. ASSUME NEW p \in TranExclusive(mm) PROVE H(p) = CombinedFreshQdLrnsId(p)
      <4>1. p \in Messages  BY TranSubMessages DEF TranExclusive
      <4>2. lev(p) < lev(mm)  BY TranExclusiveDecreasesTranSize
      <4>3. lev(p) \in Nat  BY <4>1, TranCardNat
      <4>4. lev(p) \in 0..(n-1)  BY <4>2, <4>3, SMT
      <4> QED BY <4>1, <4>4
    <3> QED BY <3>1
  <2> QED BY <2>1, <2>2, <2>3
<1> QED BY <1>ind, GeneralNatInduction, IsaM("blast")

LEMMA CflId ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic, NEW p \in Messages
  PROVE CombinedFreshQdLrnsId(p).id = p
<1>1. CombinedFreshQdLrnsId(p)
        = CombinedFreshQdLrnsIdR(p, {CombinedFreshQdLrnsId(q) : q \in TranExclusive(p)})
  BY CombinedFreshQdLrnsIdRec
<1> QED BY <1>1 DEF CombinedFreshQdLrnsIdR

\* Qd(alpha, m, d) is the set of strict ancestors of m of matching ballot at
\* depth d-1.  Proof: unfold CombinedFreshQdLrnsId(m) via CombinedFreshQdLrnsIdRec, read off the qd
\* field at <<alpha,d>>, identify each recursive result y with its id (CflId),
\* and observe the qd comprehension's d=1 / d>1 conditions are exactly
\* HasDepth(.,.,d-1). Mirrors HPaxos.tla's QdRec (with outer/inner variable
\* names swapped: here the outer/self message is m, the ancestor being
\* filtered is x).
LEMMA QdDef ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         NEW alpha \in Learners,
         NEW m \in Messages,
         NEW d \in Nat
  PROVE Qd(alpha, m, d) = CombinedFreshQdLrnsId(m).qd[<<alpha, d>>]
<1> DEFINE RR == {CombinedFreshQdLrnsId(p) : p \in TranExclusive(m)}
<1> DEFINE cond(mm) == /\ d > 0
                       /\ B(mm.id) = B(m)
                       /\ Sig(mm.id) \in Acceptors
                       /\ d = 1 => (IsOneB(mm.id) /\ mm.fresh[alpha])
                       /\ d > 1 => SigS(mm.qd[<<alpha, d-1>>]) \in Quorums(alpha)
<1>rec. CombinedFreshQdLrnsId(m) = CombinedFreshQdLrnsIdR(m, RR)  BY CombinedFreshQdLrnsIdRec
<1>dom. <<alpha, d>> \in Learners \X Nat  OBVIOUS
<1>raw. CombinedFreshQdLrnsId(m).qd[<<alpha, d>>] = {y.id : y \in {mm \in RR : cond(mm)}}
  BY <1>rec, <1>dom DEF CombinedFreshQdLrnsIdR
<1>2. {y.id : y \in {mm \in RR : cond(mm)}} \subseteq Qd(alpha, m, d)
  <2> SUFFICES ASSUME NEW z \in {y.id : y \in {mm \in RR : cond(mm)}} PROVE z \in Qd(alpha, m, d)  OBVIOUS
  <2>1. PICK y \in {mm \in RR : cond(mm)} : z = y.id  OBVIOUS
  <2>2. y \in RR /\ cond(y)  BY <2>1
  <2>3. PICK p \in TranExclusive(m) : y = CombinedFreshQdLrnsId(p)  BY <2>2
  <2>4. p \in Messages  BY <2>3, TranSubMessages DEF TranExclusive
  <2>5. y.id = p  BY <2>3, <2>4, CflId
  <2>6. z = p  BY <2>1, <2>5
  <2>9. /\ d > 0 /\ B(p) = B(m) /\ Sig(p) \in Acceptors
        /\ (d = 1 => (IsOneB(p) /\ CombinedFreshQdLrnsId(p).fresh[alpha]))
        /\ (d > 1 => SigS(CombinedFreshQdLrnsId(p).qd[<<alpha, d-1>>]) \in Quorums(alpha))
    BY <2>2, <2>3, <2>5
  <2>10. HasDepth(alpha, p, d-1)  BY <2>9 DEF HasDepth
  <2> QED BY <2>3, <2>6, <2>9, <2>10 DEF Qd
<1>3. Qd(alpha, m, d) \subseteq {y.id : y \in {mm \in RR : cond(mm)}}
  <2> SUFFICES ASSUME NEW z \in Qd(alpha, m, d) PROVE z \in {y.id : y \in {mm \in RR : cond(mm)}}  OBVIOUS
  <2>1. z \in TranExclusive(m) /\ d > 0 /\ B(m) = B(z) /\ HasDepth(alpha, z, d-1)  BY DEF Qd
  <2>2. z \in Messages  BY <2>1, TranSubMessages DEF TranExclusive
  <2> DEFINE y == CombinedFreshQdLrnsId(z)
  <2>3. y \in RR  BY <2>1
  <2>4. y.id = z  BY <2>2, CflId
  <2>7. /\ Sig(z) \in Acceptors
        /\ d = 1 => (IsOneB(z) /\ y.fresh[alpha])
        /\ d > 1 => SigS(y.qd[<<alpha, d-1>>]) \in Quorums(alpha)
    BY <2>1 DEF HasDepth
  <2>8. cond(y)  BY <2>1, <2>4, <2>7
  <2>9. y \in {mm \in RR : cond(mm)}  BY <2>3, <2>8
  <2> QED BY <2>9, <2>4
<1> QED BY <1>raw, <1>2, <1>3

\* The lrns field records the learners alpha whose depth-1 quorum (SigS(Qd(.,.,1)))
\* is a quorum -- which is exactly HasDepth(alpha, m, 1) under the current HasDepth.
\* Proof: unfold via CombinedFreshQdLrnsIdRec; the lrns field's qdx is the same as
\* the qd field, so SigS(qdx[<<alpha,1>>]) = SigS(Qd(alpha,m,1)). Mirrors
\* HPaxos.tla's LrnsDef.
LEMMA LrnsDef ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic, NEW m \in Messages
  PROVE Lrns(m) = CombinedFreshQdLrnsId(m).lrns
<1>1. Lrns(m) = {alpha \in Learners : Sig(m) \in Acceptors /\ SigS(CombinedFreshQdLrnsId(m).qd[<<alpha, 1>>]) \in Quorums(alpha)}
  BY DEF Lrns, HasDepth
<1>2. CombinedFreshQdLrnsId(m).lrns = {alpha \in Learners : Sig(m) \in Acceptors /\ SigS(CombinedFreshQdLrnsId(m).qd[<<alpha, 1>>]) \in Quorums(alpha)}
  <2>1. CombinedFreshQdLrnsId(m) = CombinedFreshQdLrnsIdR(m, {CombinedFreshQdLrnsId(p) : p \in TranExclusive(m)})
    BY CombinedFreshQdLrnsIdRec
  <2> QED BY <2>1 DEF CombinedFreshQdLrnsIdR
<1> QED BY <1>1, <1>2

\* Fresh unfolded.  The fresh field quantifies over the strict closure r =
\* TranExclusive(m), identifying each recursive result with its id/lrns (CflId,
\* DEF Lrns).  The inner \E ranges over TranExclusive(m) (matching the field);
\* the outer \A can stay over Tran(m) since the extra x = m case is trivially
\* satisfied by V(m) = V(m). Mirrors HPaxos.tla's FreshDef.
LEMMA FreshDef ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         NEW alpha \in Learners,
         NEW m \in Messages
  PROVE Fresh(alpha, m) = CombinedFreshQdLrnsId(m).fresh[alpha]
<1> DEFINE RR == {CombinedFreshQdLrnsId(p) : p \in TranExclusive(m)}
<1> DEFINE FF(mm) == \/ V(mm.id) = V(m)
                     \/ Con(alpha, m) \cap mm.lrns = {}
                     \/ \E pp \in RR: B(pp.id) > B(mm.id) /\ Con(alpha, m) \cap pp.lrns # {}
<1> DEFINE GG(q) == \/ V(q) = V(m)
                    \/ Con(alpha, m) \cap Lrns(q) = {}
                    \/ \E p \in TranExclusive(m): B(p) > B(q) /\ Con(alpha, m) \cap Lrns(p) # {}
<1>rec. CombinedFreshQdLrnsId(m) = CombinedFreshQdLrnsIdR(m, RR)  BY CombinedFreshQdLrnsIdRec
<1>raw. CombinedFreshQdLrnsId(m).fresh[alpha] = (\A mm \in RR : FF(mm))
  BY <1>rec DEF CombinedFreshQdLrnsIdR
<1>id. \A q \in TranExclusive(m) : /\ CombinedFreshQdLrnsId(q).id = q
                                  /\ CombinedFreshQdLrnsId(q).lrns = Lrns(q)
  <2> SUFFICES ASSUME NEW q \in TranExclusive(m) PROVE /\ CombinedFreshQdLrnsId(q).id = q
                                                      /\ CombinedFreshQdLrnsId(q).lrns = Lrns(q)  OBVIOUS
  <2>1. q \in Messages  BY TranSubMessages DEF TranExclusive
  <2>2. CombinedFreshQdLrnsId(q).id = q  BY <2>1, CflId
  <2>3. CombinedFreshQdLrnsId(q).lrns = Lrns(q)  BY <2>1, LrnsDef
  <2> QED BY <2>2, <2>3
<1>ex. \A q \in TranExclusive(m) :
          (\E pp \in RR: B(pp.id) > B(q) /\ Con(alpha, m) \cap pp.lrns # {})
          <=> (\E p \in TranExclusive(m): B(p) > B(q) /\ Con(alpha, m) \cap Lrns(p) # {})
  <2> SUFFICES ASSUME NEW q \in TranExclusive(m) PROVE
          (\E pp \in RR: B(pp.id) > B(q) /\ Con(alpha, m) \cap pp.lrns # {})
          <=> (\E p \in TranExclusive(m): B(p) > B(q) /\ Con(alpha, m) \cap Lrns(p) # {})  OBVIOUS
  <2>1. ASSUME NEW pp \in RR, B(pp.id) > B(q), Con(alpha, m) \cap pp.lrns # {}
        PROVE \E p \in TranExclusive(m): B(p) > B(q) /\ Con(alpha, m) \cap Lrns(p) # {}
    <3>1. PICK p \in TranExclusive(m) : pp = CombinedFreshQdLrnsId(p)  BY <2>1
    <3>2. pp.id = p /\ pp.lrns = Lrns(p)  BY <3>1, <1>id
    <3> QED BY <2>1, <3>2
  <2>2. ASSUME NEW p \in TranExclusive(m), B(p) > B(q), Con(alpha, m) \cap Lrns(p) # {}
        PROVE \E pp \in RR: B(pp.id) > B(q) /\ Con(alpha, m) \cap pp.lrns # {}
    <3>1. CombinedFreshQdLrnsId(p) \in RR  BY <2>2
    <3>2. CombinedFreshQdLrnsId(p).id = p /\ CombinedFreshQdLrnsId(p).lrns = Lrns(p)  BY <2>2, <1>id
    <3> QED BY <2>2, <3>1, <3>2
  <2> QED BY <2>1, <2>2
<1>gg. \A q \in TranExclusive(m) : FF(CombinedFreshQdLrnsId(q)) <=> GG(q)
  <2> SUFFICES ASSUME NEW q \in TranExclusive(m) PROVE FF(CombinedFreshQdLrnsId(q)) <=> GG(q)  OBVIOUS
  <2>1. CombinedFreshQdLrnsId(q).id = q /\ CombinedFreshQdLrnsId(q).lrns = Lrns(q)  BY <1>id
  <2>2. (\E pp \in RR: B(pp.id) > B(CombinedFreshQdLrnsId(q).id) /\ Con(alpha, m) \cap pp.lrns # {})
        <=> (\E p \in TranExclusive(m): B(p) > B(q) /\ Con(alpha, m) \cap Lrns(p) # {})
    BY <1>ex, <2>1
  <2> QED BY <2>1, <2>2
<1>2. (\A mm \in RR : FF(mm)) <=> (\A q \in TranExclusive(m) : GG(q))
  <2>1. ASSUME \A mm \in RR : FF(mm), NEW q \in TranExclusive(m) PROVE GG(q)
    <3>1. CombinedFreshQdLrnsId(q) \in RR  OBVIOUS
    <3> QED BY <2>1, <3>1, <1>gg
  <2>2. ASSUME \A q \in TranExclusive(m) : GG(q), NEW mm \in RR PROVE FF(mm)
    <3>1. PICK q \in TranExclusive(m) : mm = CombinedFreshQdLrnsId(q)  BY <2>2
    <3> QED BY <2>2, <3>1, <1>gg
  <2> QED BY <2>1, <2>2
<1>m. m \in Tran(m)  BY DEF Tran
<1>raw2. CombinedFreshQdLrnsId(m).fresh[alpha] = (\A q \in TranExclusive(m) : GG(q))  BY <1>raw, <1>2
<1>4. (\A x \in Tran(m) : GG(x)) <=> (\A q \in TranExclusive(m) : GG(q))
  <2>1. Tran(m) = TranExclusive(m) \cup {m}  BY <1>m DEF TranExclusive
  <2>2. GG(m)  OBVIOUS
  <2> QED BY <2>1, <2>2
<1>fresh. Fresh(alpha, m) = (\A x \in Tran(m) : GG(x))  BY DEF Fresh
<1> QED BY <1>raw2, <1>4, <1>fresh

\* HasDepth is defined directly via the raw CombinedFreshQdLrnsId fields;
\* this shows it agrees with the "nice formula" Fresh/Qd operators, by
\* substituting FreshDef and QdDef into HasDepth's own definition.
LEMMA HasDepthDef ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         NEW alpha \in Learners, NEW x \in Messages, NEW d \in Nat
  PROVE HasDepth(alpha, x, d) = 
          /\ Sig(x) \in Acceptors
          /\ IF d=0 THEN (IsOneB(x) /\ Fresh(alpha, x))
                    ELSE SigS(Qd(alpha, x, d)) \in Quorums(alpha)
<1>f. Fresh(alpha, x) = CombinedFreshQdLrnsId(x).fresh[alpha]  BY FreshDef
<1>q. Qd(alpha, x, d) = CombinedFreshQdLrnsId(x).qd[<<alpha, d>>]  BY QdDef
<1> QED BY <1>f, <1>q DEF HasDepth

\* If m has more than one Prev, two distinct maximal same-signer ancestors of m
\* are pairwise incomparable (each lies outside the other's Tran, by Prev's own
\* maximality clause plus matching signatures), which is exactly what it means
\* for Sig(m) to be Caught. Extracted standalone version of the key step buried
\* inside HPaxos.tla's AtMostOnePrev (its <1>uniq/<2>6), for the "more than one"
\* direction directly, via Cardinality rather than two named witnesses. Requires
\* Sig(m) \in Acceptors (Caught/CaughtS only ever contains Acceptors), matching
\* AtMostOnePrev's own ASSUME NEW m \in Message, Sig(m) \in Acceptor.
LEMMA MultiplePrevImpliesCaught ==
  ASSUME TranFinite, NEW m \in Messages,
         Sig(m) \in Acceptors, Cardinality(Prev(m)) > 1
  PROVE Sig(m) \in Caught(m)
<1>subT. Prev(m) \subseteq Tran(m)  BY DEF Prev, TranExclusive
<1>finT. IsFiniteSet(Tran(m))  BY DEF TranFinite
<1>fin. IsFiniteSet(Prev(m))  BY <1>subT, <1>finT, FS_Subset
<1>cardNat. Cardinality(Prev(m)) \in Nat  BY <1>fin, FS_CardinalityType
<1>ne. Prev(m) # {}  BY FS_EmptySet
<1>x1. PICK x1 \in Prev(m) : TRUE  BY <1>ne
<1>rem. IsFiniteSet(Prev(m) \ {x1}) /\ Cardinality(Prev(m) \ {x1}) = Cardinality(Prev(m)) - 1
  BY <1>fin, <1>x1, FS_RemoveElement
<1>ne2. Prev(m) \ {x1} # {}
  <2>1. Cardinality(Prev(m) \ {x1}) > 0  BY <1>rem, <1>cardNat, SMT
  <2> QED BY <2>1, FS_EmptySet
<1>x2. PICK x2 \in Prev(m) \ {x1} : TRUE  BY <1>ne2
<1>x2In. x2 \in Prev(m) /\ x2 # x1  BY <1>x2
<1>1. x1 \in TranExclusive(m) /\ Sig(x1) = Sig(m)
      /\ \A y \in TranExclusive(m): x1 \in TranExclusive(y) => Sig(x1) # Sig(y)  BY <1>x1 DEF Prev
<1>2. x2 \in TranExclusive(m) /\ Sig(x2) = Sig(m)
      /\ \A y \in TranExclusive(m): x2 \in TranExclusive(y) => Sig(x2) # Sig(y)  BY <1>x2In DEF Prev
<1>3. x1 \in Tran(m) /\ x2 \in Tran(m)  BY <1>1, <1>2 DEF TranExclusive
<1>4. x1 \notin Tran(x2)  BY <1>1, <1>2, <1>x2In DEF TranExclusive
<1>5. x2 \notin Tran(x1)  BY <1>1, <1>2, <1>x2In DEF TranExclusive
<1>6. \E m1 \in Tran(m): \E m2 \in Tran(m):
        Sig(m1) = Sig(m) /\ Sig(m2) = Sig(m) /\ m1 \notin Tran(m2) /\ m2 \notin Tran(m1)
  BY <1>1, <1>2, <1>3, <1>4, <1>5
<1> QED BY <1>6 DEF Caught, CaughtS


\* Tran is antisymmetric. MI has no WellFormed/Message split like HPaxos.tla, so
\* this is derived directly from TranAcyclic rather than needing a separate axiom.
LEMMA TranAntisym ==
  ASSUME TranAcyclic, NEW p \in Messages, NEW q \in Messages,
         p \in Tran(q), q \in Tran(p)
  PROVE p = q
<1> SUFFICES ASSUME p # q PROVE FALSE  OBVIOUS
<1>1. p \in TranExclusive(q)  BY DEF TranExclusive
<1> QED BY <1>1 DEF TranAcyclic

\* Same-signature domination: any same-sig strict ancestor is below some Prev.
LEMMA PrevDom ==
  ASSUME TypeOKMessageInterface, TranFinite, TranTrans, TranAcyclic,
         NEW z \in Messages, NEW x \in TranExclusive(z), Sig(x) = Sig(z)
  PROVE \E q \in Prev(z) : x \in Tran(q)
<1> DEFINE U == {y \in TranExclusive(z) : Sig(y) = Sig(z) /\ x \in Tran(y)}
<1>xx. x \in Tran(x)  BY DEF Tran
<1>1. x \in U  BY <1>xx
<1>2. U \subseteq Messages
  <2> SUFFICES ASSUME NEW y \in U PROVE y \in Messages  OBVIOUS
  <2>1. y \in Tran(z)  BY DEF TranExclusive
  <2> QED BY <2>1, TranSubMessages
<1>3. IsFiniteSet(U)
  <2>1. IsFiniteSet(Tran(z))  BY DEF TranFinite
  <2>2. U \subseteq Tran(z)  BY DEF TranExclusive
  <2> QED BY <2>1, <2>2, FS_Subset
<1>4. PICK q \in U : \A y \in U : Cardinality(Tran(y)) <= Cardinality(Tran(q))
  BY <1>1, <1>2, <1>3, TranMaxExists
<1>5. q \in TranExclusive(z) /\ Sig(q) = Sig(z) /\ x \in Tran(q)  BY <1>4
<1>7. q \in Prev(z)
  <2> SUFFICES \A y \in TranExclusive(z): q \in TranExclusive(y) => Sig(q) # Sig(y)
    BY <1>5 DEF Prev
  <2> SUFFICES ASSUME NEW y \in TranExclusive(z), q \in TranExclusive(y), Sig(q) = Sig(y)
               PROVE FALSE  OBVIOUS
  <2>0. q \in Tran(y) /\ q # y  BY DEF TranExclusive
  <2>0b. Sig(y) = Sig(z)  BY <1>5
  <2>1. y \in Messages  BY TranSubMessages DEF TranExclusive
  <2>2. x \in Tran(y)
    <3>1. Tran(q) \subseteq Tran(y)  BY <2>0, <2>1, TranTrans DEF TranTrans
    <3> QED BY <1>5, <3>1
  <2>3. y \in U  BY <2>2, <2>0b
  <2>4. Cardinality(Tran(y)) <= Cardinality(Tran(q))  BY <2>3, <1>4
  <2>6. Cardinality(Tran(q)) < Cardinality(Tran(y))  BY <2>0, <2>1, TranExclusiveDecreasesTranSize
  <2>qm. q \in Messages  BY <1>2, <1>4
  <2>7. Cardinality(Tran(q)) \in Nat /\ Cardinality(Tran(y)) \in Nat  BY <2>qm, <2>1, TranCardNat
  <2> QED BY <2>4, <2>6, <2>7, SMT
<1> QED BY <1>5, <1>7

\* Weaker, well-formedness-free substitute for "Prev has at most one element"
\* (which would need an axiom this file doesn't have, e.g. HPaxos.tla's
\* WellFormed): two elements of the SAME Prev(m) that happen to be comparable
\* (one in the other's Tran) must be equal, directly from Prev's own
\* maximality clause -- no assumption about Sig(m) needed.
LEMMA PrevComparableEqual ==
  ASSUME NEW m \in Messages,
         NEW x1 \in Prev(m), NEW x2 \in Prev(m), x1 \in Tran(x2)
  PROVE x1 = x2
<1> SUFFICES ASSUME x1 # x2 PROVE FALSE  OBVIOUS
<1>1. x1 \in TranExclusive(m) /\ Sig(x1) = Sig(m)
      /\ \A y \in TranExclusive(m): x1 \in TranExclusive(y) => Sig(x1) # Sig(y)  BY DEF Prev
<1>2. x2 \in TranExclusive(m) /\ Sig(x2) = Sig(m)  BY DEF Prev
<1>3. x1 \in TranExclusive(x2)  BY DEF TranExclusive
<1>4. Sig(x1) # Sig(x2)  BY <1>1, <1>2, <1>3
<1> QED BY <1>1, <1>2, <1>4

\* Easy direction: distinct same-sig m1,m2 sharing a Prev witness (or both
\* having empty Prev) are incomparable. The "both empty" disjunct handles the
\* base/genesis case (e.g. two same-signer messages with no prior same-signer
\* history at all) that a plain nonempty-intersection condition misses -- see
\* CaughtPrev's comment for why the naive Prev(m1)=Prev(m2) / intersection-only
\* characterizations are each individually wrong here without well-formedness.
LEMMA CaughtPrevEasy ==
  ASSUME TypeOKMessageInterface, TranFinite, TranTrans, TranAcyclic, NEW a \in Acceptors,
         NEW m1 \in Messages, NEW m2 \in Messages,
         Sig(m1) = a, Sig(m2) = a, m1 # m2,
         (Prev(m1) = {} /\ Prev(m2) = {}) \/ (Prev(m1) \cap Prev(m2) # {})
  PROVE m1 \notin Tran(m2) /\ m2 \notin Tran(m1)
<1>1. CASE Prev(m1) = {} /\ Prev(m2) = {}
  <2>a. m1 \notin Tran(m2)
    <3> SUFFICES ASSUME m1 \in Tran(m2) PROVE FALSE  OBVIOUS
    <3>1. m1 \in TranExclusive(m2)  BY DEF TranExclusive
    <3>2. \E q \in Prev(m2) : m1 \in Tran(q)  BY <3>1, PrevDom
    <3> QED BY <3>2, <1>1
  <2>b. m2 \notin Tran(m1)
    <3> SUFFICES ASSUME m2 \in Tran(m1) PROVE FALSE  OBVIOUS
    <3>1. m2 \in TranExclusive(m1)  BY DEF TranExclusive
    <3>2. \E q \in Prev(m1) : m2 \in Tran(q)  BY <3>1, PrevDom
    <3> QED BY <3>2, <1>1
  <2> QED BY <2>a, <2>b
<1>2. CASE Prev(m1) \cap Prev(m2) # {}
  <2>q. PICK q \in Prev(m1) \cap Prev(m2) : TRUE  BY <1>2
  <2>qm1. q \in Prev(m1)  BY <2>q
  <2>qm2. q \in Prev(m2)  BY <2>q
  <2>a. m1 \notin Tran(m2)
    <3> SUFFICES ASSUME m1 \in Tran(m2) PROVE FALSE  OBVIOUS
    <3>1. q \in TranExclusive(m1) /\ Sig(q) = Sig(m1)  BY <2>qm1 DEF Prev
    <3>2. m1 \in TranExclusive(m2)  BY DEF TranExclusive
    <3>3. \A y \in TranExclusive(m2): q \in TranExclusive(y) => Sig(q) # Sig(y)
      BY <2>qm2 DEF Prev
    <3>4. Sig(q) # Sig(m1)  BY <3>1, <3>2, <3>3
    <3> QED BY <3>1, <3>4
  <2>b. m2 \notin Tran(m1)
    <3> SUFFICES ASSUME m2 \in Tran(m1) PROVE FALSE  OBVIOUS
    <3>1. q \in TranExclusive(m2) /\ Sig(q) = Sig(m2)  BY <2>qm2 DEF Prev
    <3>2. m2 \in TranExclusive(m1)  BY DEF TranExclusive
    <3>3. \A y \in TranExclusive(m1): q \in TranExclusive(y) => Sig(q) # Sig(y)
      BY <2>qm1 DEF Prev
    <3>4. Sig(q) # Sig(m2)  BY <3>1, <3>2, <3>3
    <3> QED BY <3>1, <3>4
  <2> QED BY <2>a, <2>b
<1> QED BY <1>1, <1>2

\* Hard direction: any incomparable same-sig pair in a transitively-closed m
\* reduces, by strong induction on the summed Tran-size measure, to a pair
\* satisfying the (both empty) \/ (intersection) target. Ports HPaxos.tla's
\* CaughtPrevHard; the one branch that needed PrevUnique (well-formedness)
\* there is replaced by PrevComparableEqual, which suffices once the two
\* candidate witnesses are shown comparable via the Tran-chain.
LEMMA CaughtPrevHard ==
  ASSUME TypeOKMessageInterface, TranFinite, TranTrans, TranAcyclic,
         NEW m \in SUBSET Messages, \A xx \in m: TranExclusive(xx) \subseteq m,
         NEW a \in Acceptors, NEW pp1 \in m, NEW pp2 \in m,
         Sig(pp1) = a, Sig(pp2) = a, pp1 \notin Tran(pp2), pp2 \notin Tran(pp1)
  PROVE \E q1 \in m: \E q2 \in m: Sig(q1) = a /\ Sig(q2) = a /\ q1 # q2 /\
          ((Prev(q1) = {} /\ Prev(q2) = {}) \/ (Prev(q1) \cap Prev(q2) # {}))
<1> DEFINE lev(z) == Cardinality(Tran(z))
<1> DEFINE Fork == \E q1 \in m: \E q2 \in m: Sig(q1)=a /\ Sig(q2)=a /\ q1 # q2 /\
          ((Prev(q1) = {} /\ Prev(q2) = {}) \/ (Prev(q1) \cap Prev(q2) # {}))
<1> DEFINE IncPair(z1,z2) == /\ z1 \in m /\ z2 \in m /\ Sig(z1)=a /\ Sig(z2)=a
                            /\ z1 \notin Tran(z2) /\ z2 \notin Tran(z1)
<1> DEFINE Q(n) == \A z1, z2 : (IncPair(z1,z2) /\ lev(z1)+lev(z2) = n) => Fork
<1>mM. m \subseteq Messages  OBVIOUS
<1>levfacts. \A z \in m : z \in Messages /\ lev(z) \in Nat
  <2> SUFFICES ASSUME NEW z \in m PROVE z \in Messages /\ lev(z) \in Nat  OBVIOUS
  <2>1. z \in Messages  BY <1>mM
  <2> QED BY <2>1, TranCardNat
<1> SUFFICES \A n \in Nat : Q(n)
  <2>1. IncPair(pp1, pp2)  BY DEF IncPair
  <2>2. lev(pp1) + lev(pp2) \in Nat  BY <1>levfacts
  <2> QED BY <2>1, <2>2
<1> HIDE DEF Q
<1>ind. \A n \in Nat : (\A k \in 0..(n-1) : Q(k)) => Q(n)
  <2> USE DEF Q, IncPair, Fork
  <2> SUFFICES ASSUME NEW n \in Nat, \A k \in 0..(n-1) : Q(k),
                      NEW x1, NEW x2, IncPair(x1,x2), lev(x1)+lev(x2) = n
               PROVE  Fork
    OBVIOUS
  <2>x. x1 \in m /\ x2 \in m /\ Sig(x1) = a /\ Sig(x2) = a
        /\ x1 \notin Tran(x2) /\ x2 \notin Tran(x1)  OBVIOUS
  <2>mc. x1 \in Messages /\ x2 \in Messages  BY <2>x, <1>levfacts
  <2>lev. lev(x1) \in Nat /\ lev(x2) \in Nat  BY <2>x, <1>levfacts
  <2>ne. x1 # x2  BY <2>x DEF Tran
  <2>base. CASE Prev(x1) = {} /\ Prev(x2) = {}  BY <2>x, <2>ne, <2>base
  <2>nb. CASE ~(Prev(x1) = {} /\ Prev(x2) = {})
    <3>a. CASE Prev(x1) # {}
      <4>1. PICK q1 \in Prev(x1) : TRUE  BY <3>a
      <4>2. q1 \in TranExclusive(x1) /\ Sig(q1) = a  BY <4>1, <2>x DEF Prev
      <4>3. q1 \in Tran(x1) /\ q1 # x1  BY <4>2 DEF TranExclusive
      <4>4. q1 \in m
        <5>1. TranExclusive(x1) \subseteq m  BY <2>x
        <5> QED BY <4>2, <5>1
      <4>mc. q1 \in Messages /\ lev(q1) \in Nat  BY <4>4, <1>levfacts
      <4>5. lev(q1) < lev(x1)  BY <2>mc, <4>2, TranExclusiveDecreasesTranSize
      <4>6. x2 \notin Tran(q1)
        <5> SUFFICES ASSUME x2 \in Tran(q1) PROVE FALSE  OBVIOUS
        <5>1. Tran(q1) \subseteq Tran(x1)  BY <4>3, <2>mc, TranTrans DEF TranTrans
        <5> QED BY <5>1, <2>x
      <4>7. CASE q1 \notin Tran(x2)
        <5>1. IncPair(q1, x2)  BY <4>2, <4>4, <4>6, <4>7, <2>x
        <5>2. lev(q1) + lev(x2) \in 0..(n-1)  BY <4>5, <4>mc, <2>lev
        <5>3. Q(lev(q1) + lev(x2))  BY <5>2
        <5> QED BY <5>1, <5>3
      <4>8. CASE q1 \in Tran(x2)
        <5>1. q1 # x2  BY <4>3, <2>x
        <5>2. q1 \in TranExclusive(x2)  BY <4>8, <5>1 DEF TranExclusive
        <5>3. PICK r \in Prev(x2) : q1 \in Tran(r)  BY <5>2, <4>2, <2>mc, PrevDom
        <5>4. r \in TranExclusive(x2) /\ Sig(r) = a  BY <5>3, <2>x DEF Prev
        <5>5. r \in Tran(x2) /\ r # x2  BY <5>4 DEF TranExclusive
        <5>6. r \in m
          <6>1. TranExclusive(x2) \subseteq m  BY <2>x
          <6> QED BY <5>4, <6>1
        <5>mc. r \in Messages /\ lev(r) \in Nat  BY <5>6, <1>levfacts
        <5>7. lev(r) < lev(x2)  BY <2>mc, <5>4, TranExclusiveDecreasesTranSize
        <5>8. x1 \notin Tran(r)
          <6> SUFFICES ASSUME x1 \in Tran(r) PROVE FALSE  OBVIOUS
          <6>1. Tran(r) \subseteq Tran(x2)  BY <5>5, <2>mc, TranTrans DEF TranTrans
          <6> QED BY <6>1, <2>x
        <5>9. CASE r \notin Tran(x1)
          <6>1. IncPair(x1, r)  BY <5>4, <5>6, <5>8, <5>9, <2>x
          <6>2. lev(x1) + lev(r) \in 0..(n-1)  BY <5>7, <5>mc, <2>lev
          <6>3. Q(lev(x1) + lev(r))  BY <6>2
          <6> QED BY <6>1, <6>3
        <5>10. CASE r \in Tran(x1)
          <6>1. r \in TranExclusive(x1)  BY <5>5, <5>10, <2>x DEF TranExclusive
          <6>2. Sig(r) = Sig(x1)  BY <5>4, <2>x
          <6>3. PICK s \in Prev(x1) : r \in Tran(s)  BY <6>1, <6>2, <2>mc, PrevDom
          <6>sm. s \in m
            <7>1. s \in TranExclusive(x1)  BY <6>3 DEF Prev
            <7>2. TranExclusive(x1) \subseteq m  OBVIOUS
            <7> QED BY <7>1, <7>2
          <6>smc. s \in Messages /\ lev(s) \in Nat  BY <6>sm, <1>levfacts
          <6>4. Tran(r) \subseteq Tran(s)  BY <6>3, <6>smc, TranTrans DEF TranTrans
          <6>5. q1 \in Tran(s)  BY <5>3, <6>4
          <6>6. q1 = s  BY <4>1, <6>3, <6>5, PrevComparableEqual
          <6>7. r \in Tran(q1)  BY <6>3, <6>6
          <6>8. q1 \in Tran(r)  BY <5>3
          <6>9. q1 = r
            <7>1. q1 \in Messages  BY <4>4, <1>levfacts
            <7>2. r \in Messages  BY <5>6, <1>levfacts
            <7> QED BY <6>7, <6>8, <7>1, <7>2, TranAntisym
          <6>10. q1 \in Prev(x1) \cap Prev(x2)
            <7>1. q1 \in Prev(x2)  BY <5>3, <6>9
            <7> QED BY <4>1, <7>1
          <6>11. IncPair(x1, x2) /\ ((Prev(x1)={}/\Prev(x2)={}) \/ (Prev(x1)\cap Prev(x2)#{}))
            BY <2>x, <6>10
          <6> QED BY <6>11, <2>ne
        <5> QED BY <5>9, <5>10
      <4> QED BY <4>7, <4>8
    <3>b. CASE Prev(x1) = {}
      <4>0. Prev(x2) # {}  BY <2>nb, <3>b
      <4>1. PICK q2 \in Prev(x2) : TRUE  BY <4>0
      <4>2. q2 \in TranExclusive(x2) /\ Sig(q2) = a  BY <4>1, <2>x DEF Prev
      <4>3. q2 \in Tran(x2) /\ q2 # x2  BY <4>2 DEF TranExclusive
      <4>4. q2 \in m
        <5>1. TranExclusive(x2) \subseteq m  BY <2>x
        <5> QED BY <4>2, <5>1
      <4>mc. q2 \in Messages /\ lev(q2) \in Nat  BY <4>4, <1>levfacts
      <4>5. lev(q2) < lev(x2)  BY <2>mc, <4>2, TranExclusiveDecreasesTranSize
      <4>6. x1 \notin Tran(q2)
        <5> SUFFICES ASSUME x1 \in Tran(q2) PROVE FALSE  OBVIOUS
        <5>1. Tran(q2) \subseteq Tran(x2)  BY <4>3, <2>mc, TranTrans DEF TranTrans
        <5> QED BY <5>1, <2>x
      <4>7. CASE q2 \notin Tran(x1)
        <5>1. IncPair(x1, q2)  BY <4>2, <4>4, <4>6, <4>7, <2>x
        <5>2. lev(x1) + lev(q2) \in 0..(n-1)  BY <4>5, <4>mc, <2>lev
        <5>3. Q(lev(x1) + lev(q2))  BY <5>2
        <5> QED BY <5>1, <5>3
      <4>8. CASE q2 \in Tran(x1)
        <5>1. q2 # x1  BY <4>3, <2>x
        <5>2. q2 \in TranExclusive(x1)  BY <4>8, <5>1 DEF TranExclusive
        <5>3. PICK r \in Prev(x1) : q2 \in Tran(r)  BY <5>2, <4>2, <2>mc, PrevDom
        <5>4. r \in TranExclusive(x1) /\ Sig(r) = a  BY <5>3, <2>x DEF Prev
        <5>5. r \in Tran(x1) /\ r # x1  BY <5>4 DEF TranExclusive
        <5>6. r \in m
          <6>1. TranExclusive(x1) \subseteq m  BY <2>x
          <6> QED BY <5>4, <6>1
        <5>mc. r \in Messages /\ lev(r) \in Nat  BY <5>6, <1>levfacts
        <5>7. lev(r) < lev(x1)  BY <2>mc, <5>4, TranExclusiveDecreasesTranSize
        <5>8. x2 \notin Tran(r)
          <6> SUFFICES ASSUME x2 \in Tran(r) PROVE FALSE  OBVIOUS
          <6>1. Tran(r) \subseteq Tran(x1)  BY <5>5, <2>mc, TranTrans DEF TranTrans
          <6> QED BY <6>1, <2>x
        <5>9. CASE r \notin Tran(x2)
          <6>1. IncPair(r, x2)  BY <5>4, <5>6, <5>8, <5>9, <2>x
          <6>2. lev(r) + lev(x2) \in 0..(n-1)  BY <5>7, <5>mc, <2>lev
          <6>3. Q(lev(r) + lev(x2))  BY <6>2
          <6> QED BY <6>1, <6>3
        <5>10. CASE r \in Tran(x2)
          <6>1. r \in TranExclusive(x2)  BY <5>5, <5>10, <2>x DEF TranExclusive
          <6>2. Sig(r) = Sig(x2)  BY <5>4, <2>x
          <6>3. PICK s \in Prev(x2) : r \in Tran(s)  BY <6>1, <6>2, <2>mc, PrevDom
          <6>sm. s \in m
            <7>1. s \in TranExclusive(x2)  BY <6>3 DEF Prev
            <7>2. TranExclusive(x2) \subseteq m  OBVIOUS
            <7> QED BY <7>1, <7>2
          <6>smc. s \in Messages /\ lev(s) \in Nat  BY <6>sm, <1>levfacts
          <6>4. Tran(r) \subseteq Tran(s)  BY <6>3, <6>smc, TranTrans DEF TranTrans
          <6>5. q2 \in Tran(s)  BY <5>3, <6>4
          <6>6. q2 = s  BY <4>1, <6>3, <6>5, PrevComparableEqual
          <6>7. r \in Tran(q2)  BY <6>3, <6>6
          <6>8. q2 \in Tran(r)  BY <5>3
          <6>9. q2 = r
            <7>1. q2 \in Messages  BY <4>4, <1>levfacts
            <7>2. r \in Messages  BY <5>6, <1>levfacts
            <7> QED BY <6>7, <6>8, <7>1, <7>2, TranAntisym
          <6>10. q2 \in Prev(x1) \cap Prev(x2)
            <7>1. q2 \in Prev(x1)  BY <5>3, <6>9
            <7> QED BY <4>1, <7>1
          <6>11. IncPair(x1, x2) /\ ((Prev(x1)={}/\Prev(x2)={}) \/ (Prev(x1)\cap Prev(x2)#{}))
            BY <2>x, <6>10
          <6> QED BY <6>11, <2>ne
        <5> QED BY <5>9, <5>10
      <4> QED BY <4>7, <4>8
    <3> QED BY <3>a, <3>b
  <2> QED BY <2>base, <2>nb
<1> QED BY <1>ind, GeneralNatInduction, IsaM("blast")

\* Since MI has no well-formedness axiom ruling out "Prev has multiple
\* incomparable elements", the natural HPaxos.tla-style target
\* Prev(m1)=Prev(m2) is not always derivable, and a plain
\* Prev(m1) \cap Prev(m2) # {} target is not always TRUE: two "genesis"
\* same-signer messages with disjoint, empty histories (Tran(x)={x} for each)
\* are Caught but have Prev(x1)=Prev(x2)={}, so their intersection is empty.
\* The (both empty) \/ (intersection) disjunction below is correct in both
\* directions without needing well-formedness -- see CaughtPrevEasy/Hard.
LEMMA CaughtPrev ==
  ASSUME TypeOKMessageInterface, TranFinite, TranTrans, TranAcyclic, NEW m \in SUBSET Messages,
         \A x \in m : Tran(x) \subseteq m
  PROVE CaughtS(m) = {a \in Acceptors :
    \E m1 \in m :
    \E m2 \in m :
      /\ Sig(m1) = a
      /\ Sig(m2) = a
      /\ m1 # m2
      /\ ((Prev(m1) = {} /\ Prev(m2) = {}) \/ (Prev(m1) \cap Prev(m2) # {}))}
<1> DEFINE Target == {a \in Acceptors :
    \E m1 \in m : \E m2 \in m :
      /\ Sig(m1) = a /\ Sig(m2) = a /\ m1 # m2
      /\ ((Prev(m1) = {} /\ Prev(m2) = {}) \/ (Prev(m1) \cap Prev(m2) # {}))}
<1>mM. m \subseteq Messages  OBVIOUS
<1>te. \A xx \in m : TranExclusive(xx) \subseteq m  BY DEF TranExclusive
<1>1. CaughtS(m) \subseteq Target
  <2> SUFFICES ASSUME NEW a \in CaughtS(m) PROVE a \in Target  OBVIOUS
  <2>1. a \in Acceptors  BY DEF CaughtS
  <2>2. PICK m1 \in m, m2 \in m : Sig(m1)=a /\ Sig(m2)=a /\ m1 \notin Tran(m2) /\ m2 \notin Tran(m1)
    BY DEF CaughtS
  <2>3. \E q1 \in m: \E q2 \in m: Sig(q1)=a /\ Sig(q2)=a /\ q1 # q2 /\
          ((Prev(q1)={}/\Prev(q2)={}) \/ (Prev(q1)\cap Prev(q2)#{}))
    BY <2>1, <2>2, <1>te, CaughtPrevHard
  <2> QED BY <2>1, <2>3
<1>2. Target \subseteq CaughtS(m)
  <2> SUFFICES ASSUME NEW a \in Target PROVE a \in CaughtS(m)  OBVIOUS
  <2>1. a \in Acceptors  OBVIOUS
  <2>2. PICK m1 \in m, m2 \in m : Sig(m1)=a /\ Sig(m2)=a /\ m1#m2 /\
          ((Prev(m1)={}/\Prev(m2)={}) \/ (Prev(m1)\cap Prev(m2)#{}))  OBVIOUS
  <2>3. m1 \in Messages /\ m2 \in Messages  BY <2>2, <1>mM
  <2>4. m1 \notin Tran(m2) /\ m2 \notin Tran(m1)  BY <2>1, <2>2, <2>3, CaughtPrevEasy
  <2> QED BY <2>1, <2>2, <2>4 DEF CaughtS
<1> QED BY <1>1, <1>2

\* ===================================================================
\* Agreement: definitions and lemma skeleton
\* ===================================================================
\* Roadmap (paper "Heterogeneous Paxos 2.0", Lemma 25 "2a Agreement Better
\* Induction"; TLA+ precedent: hpaxos-tla HPaxos_2_Safety_proofs.tla,
\* HeterogeneousSpecCond/TraceExistence/TraceContradiction/ChosenSafe):
\*
\*   Suppose two decisions at ballots lobal < hibal disagree in value, with
\*   the deciding learners still connected given everything caught in the
\*   closure.  From the high decision extract a message himsg at hibal
\*   attested by the high learner.  Then build, one element per depth level,
\*   a chain of trace elements (mm_x, rr_x, ss_x, gamma_x):
\*     mm_x    a 2a-like message with lobal < B(mm_x) < B(mm_{x-1}),
\*             V(mm_x) = V(himsg), attested by gamma_x
\*     rr_x    a fresh OneB in Qd(gamma_x, mm_x, 1)
\*     ss_x    a low-side support message signed by the SAME acceptor as
\*             rr_x (obtained by intersecting a quorum of mm_x with a
\*             low-side quorum through an uncaught safety set), with
\*             ss_x \in Tran(rr_x) since that signer is uncaught
\*     gamma_x a learner in Con(alpha, rr_{x-1}) \ Con(alpha, rr_{x-2}),
\*             so the Con(alpha, rr_x) strictly grow along the chain
\*   Each mm_x is Tran-Cardinality-minimal among candidates (TraceCondCoreMin;
\*   ballots legitimately repeat within one TwoA's depth-tree, so Tran-DAG
\*   depth is the well-founded measure, not ballot), which is what makes
\*   gamma_2 provably NOT closure-connected to alpha.  The
\*   caught sets Caught(rr_x) shrink along the chain, so
\*     << Acceptors, CaughtS(closure), Caught(rr_1), .., Caught(rr_K) >>
\*   is a ValidSeqs(alpha) chain with MaxDepth(alpha)+2 pairwise-distinct
\*   ConFromCaught values -- longer than MaxDepth(alpha) allows.  FALSE.
\*
\*   The low side keeps the chain alive ("budget"): a slow decision spends
\*   one depth level per step (TraceBudgetSlow); a fast decision draws
\*   support straight from its decision set (TraceBudgetFast), which
\*   carries a quorum for every connected learner.
\*
\* All lemmas below are stated with OMITTED proofs: statements only.

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

\* Item 12, fast variant: the support message is drawn from the fast
\* decision set FS itself, which carries an l-quorum for every learner l
\* connected to alpha via any of its members -- no depth is consumed.
TraceBudgetFast(FS, seq, x) == seq[x].ss \in FS

\* TraceCondCore only reads seq at indices x, x-1 and x-2, so any two
\* sequences agreeing there (whatever their lengths) satisfy it alike.
\* (hpaxos-tla's HeterogeneousSpecCondCongr.)  Used both to transfer the
\* conditions across Append/EXCEPT and to keep minimality meaningful when
\* the ambient sequence grows.
LEMMA TraceCondCoreCongr ==
  ASSUME NEW alpha, NEW lobal, NEW CL, NEW himsg,
         NEW seq1, NEW seq2, NEW x \in Nat,
         seq1[x] = seq2[x],
         x > 1 => seq1[x-1] = seq2[x-1],
         x > 2 => seq1[x-2] = seq2[x-2]
  PROVE TraceCondCore(alpha, lobal, CL, himsg, seq1, x)
          <=> TraceCondCore(alpha, lobal, CL, himsg, seq2, x)
BY DEF TraceCondCore

\* --- learner-graph facts -------------------------------------------

\* Connectivity is symmetric: the safety sets of {alpha, beta} ARE those of
\* {beta, alpha}.
LEMMA ConFromCaughtSym ==
  ASSUME NEW alpha \in Learners, NEW beta \in Learners, NEW c
  PROVE beta \in ConFromCaught(alpha, c) <=> alpha \in ConFromCaught(beta, c)
<1>eq. {alpha, beta} = {beta, alpha}  OBVIOUS
<1>1. beta \in ConFromCaught(alpha, c) <=> \E s \in SafetySets({alpha, beta}) : s \cap c = {}
  BY DEF ConFromCaught
<1>2. alpha \in ConFromCaught(beta, c) <=> \E s \in SafetySets({beta, alpha}) : s \cap c = {}
  BY DEF ConFromCaught
<1> QED BY <1>1, <1>2, <1>eq

\* Connectivity is transitive on a condensed learner graph: the union of an
\* uncaught {alpha,beta} safety set and an uncaught {beta,gamma} safety set
\* is an uncaught {alpha,gamma} safety set.  (Paper Lemma 24's parenthetical
\* "beta \in Con_alpha(m) => Con_alpha(m) = Con_beta(m)".)
LEMMA ConFromCaughtCondensedTrans ==
  ASSUME CondensedLearnerGraphAssumption,
         NEW alpha \in Learners, NEW beta \in Learners, NEW gamma \in Learners,
         NEW c,
         beta \in ConFromCaught(alpha, c),
         gamma \in ConFromCaught(beta, c)
  PROVE gamma \in ConFromCaught(alpha, c)
<1>1. PICK s1 \in SafetySets({alpha, beta}) : s1 \cap c = {}  BY DEF ConFromCaught
<1>2. PICK s2 \in SafetySets({beta, gamma}) : s2 \cap c = {}  BY DEF ConFromCaught
<1>3. (s1 \cup s2) \in SafetySets({alpha, gamma})  BY <1>1, <1>2 DEF CondensedLearnerGraphAssumption
<1>4. (s1 \cup s2) \cap c = {}  BY <1>1, <1>2
<1> QED BY <1>3, <1>4 DEF ConFromCaught

\* With nothing caught, everyone is connected (LearnersMightAgree supplies
\* Acceptors as a safety set for every pair).
LEMMA ConFromCaughtNoneCaught ==
  ASSUME LearnersMightAgree, NEW alpha \in Learners
  PROVE ConFromCaught(alpha, {}) = Learners
<1>full. \A beta \in Learners : Acceptors \in SafetySets({alpha, beta})
  <2> SUFFICES ASSUME NEW beta \in Learners PROVE Acceptors \in SafetySets({alpha, beta})  OBVIOUS
  <2>1. <<alpha, beta>> \in Learners \X Learners  OBVIOUS
  <2>2. {alpha, beta} \in LearnerPairs  BY <2>1 DEF LearnerPairs
  <2> QED BY <2>2 DEF LearnersMightAgree
<1>sub. \A beta \in Learners : beta \in ConFromCaught(alpha, {})
  <2> SUFFICES ASSUME NEW beta \in Learners PROVE beta \in ConFromCaught(alpha, {})  OBVIOUS
  <2>1. Acceptors \in SafetySets({alpha, beta})  BY <1>full
  <2>2. Acceptors \cap {} = {}  OBVIOUS
  <2> QED BY <2>1, <2>2 DEF ConFromCaught
<1>subeq. ConFromCaught(alpha, {}) \subseteq Learners  BY DEF ConFromCaught
<1> QED BY <1>sub, <1>subeq

\* With everything caught, no one is connected: an uncaught safety set would
\* have to be empty, and empty safety sets are ruled out by
\* ValidLearnerGraphAssumption (they would have to intersect two quorums).
LEMMA ConFromCaughtAllCaught ==
  ASSUME QuorumsNonEmpty, ValidLearnerGraphAssumption, NEW alpha \in Learners
  PROVE ConFromCaught(alpha, Acceptors) = {}
<1>noempty. \A beta \in Learners : {} \notin SafetySets({alpha, beta})
  <2> SUFFICES ASSUME NEW beta \in Learners, {} \in SafetySets({alpha, beta})
               PROVE FALSE
    OBVIOUS
  <2>1. PICK q \in Quorums(alpha) : TRUE  BY DEF QuorumsNonEmpty
  <2>2. PICK r \in Quorums(beta) : TRUE  BY DEF QuorumsNonEmpty
  <2>3. ({} \cap q \cap r) # {}  BY <2>1, <2>2 DEF ValidLearnerGraphAssumption
  <2> QED BY <2>3
<1> SUFFICES ASSUME ConFromCaught(alpha, Acceptors) # {} PROVE FALSE  OBVIOUS
<1>1. PICK beta \in ConFromCaught(alpha, Acceptors) : TRUE  OBVIOUS
<1>2. beta \in Learners  BY <1>1 DEF ConFromCaught
<1>3. PICK s \in SafetySets({alpha, beta}) : s \cap Acceptors = {}  BY <1>1 DEF ConFromCaught
<1>4. s \subseteq Acceptors  BY <1>3 DEF SafetySets
<1>5. s = {}  BY <1>3, <1>4
<1> QED BY <1>3, <1>5, <1>2, <1>noempty

\* Every quorum has a member (intersect it with itself through the
\* Acceptors safety set).
LEMMA QuorumsHaveMembers ==
  ASSUME LearnersMightAgree, ValidLearnerGraphAssumption,
         NEW alpha \in Learners, NEW q \in Quorums(alpha)
  PROVE q # {}
<1>1. <<alpha, alpha>> \in Learners \X Learners  OBVIOUS
<1>2. {alpha, alpha} \in LearnerPairs  BY <1>1 DEF LearnerPairs
<1>3. Acceptors \in SafetySets({alpha, alpha})  BY <1>2 DEF LearnersMightAgree
<1>4. Acceptors \cap q \cap q # {}  BY <1>3 DEF ValidLearnerGraphAssumption
<1> QED BY <1>4

\* The central witness-extraction step: two quorums for a connected pair of
\* learners intersect in an acceptor that is not caught -- inside the safety
\* set that witnesses the connection.  (Instantiate l1 = l2 via
\* AgreementImpliesSelfAgreement when both quorums belong to one learner.)
LEMMA SafeQuorumsIntersectUncaught ==
  ASSUME ValidLearnerGraphAssumption,
         NEW l1 \in Learners, NEW l2 \in Learners,
         NEW c,
         NEW s \in SafetySets({l1, l2}), s \cap c = {},
         NEW q1 \in Quorums(l1), NEW q2 \in Quorums(l2)
  PROVE \E a \in Acceptors : a \in q1 /\ a \in q2 /\ a \notin c
<1>1. s \cap q1 \cap q2 # {}  BY DEF ValidLearnerGraphAssumption
<1>2. PICK a \in s \cap q1 \cap q2 : TRUE  BY <1>1
<1>3. a \in s /\ a \in q1 /\ a \in q2  BY <1>2
<1>4. a \notin c
  <2> SUFFICES ASSUME a \in c PROVE FALSE  OBVIOUS
  <2>1. a \in s \cap c  BY <1>3
  <2> QED BY <2>1
<1>5. a \in Acceptors
  <2>1. q1 \subseteq Acceptors  BY DEF Quorums
  <2> QED BY <1>3, <2>1
<1> QED BY <1>3, <1>4, <1>5

\* MaxDepth is the maximum over ValidSeqs lengths (minus one): no valid
\* chain exceeds it.  Packaging of the MaxDepthBound machinery from
\* LearnerGraphInterface.
LEMMA ValidSeqsLenMaxDepth ==
  ASSUME FiniteAcceptors, LearnersNonEmpty, QuorumsNonEmpty,
         LearnersMightAgree, ValidLearnerGraphAssumption,
         NEW alpha \in Learners, NEW l \in ValidSeqs(alpha)
  PROVE Len(l) - 1 <= MaxDepth(alpha)
<1> DEFINE D == {Len(s)-1 : s \in ValidSeqs(alpha)}
<1> DEFINE L == {Len(s) : s \in ValidSeqs(alpha)}
<1>accfin. IsFiniteSet(Acceptors)  BY DEF FiniteAcceptors
<1>Nnat. Cardinality(Acceptors) \in Nat  BY <1>accfin, FS_CardinalityType
<1>bound. \A s \in ValidSeqs(alpha) : Len(s) <= Cardinality(Acceptors) + 1
  <2> SUFFICES ASSUME NEW s \in ValidSeqs(alpha) PROVE Len(s) <= Cardinality(Acceptors) + 1  OBVIOUS
  <2> QED BY ValidSeqLenBoundAcceptors
<1>Lsub. L \subseteq 0..(Cardinality(Acceptors)+1)
  <2> SUFFICES ASSUME NEW k \in L PROVE k \in 0..(Cardinality(Acceptors)+1)  OBVIOUS
  <2>1. PICK s \in ValidSeqs(alpha) : k = Len(s)  OBVIOUS
  <2>2. Len(s) \in Nat  BY <2>1 DEF ValidSeqs
  <2>3. Len(s) <= Cardinality(Acceptors) + 1  BY <2>1, <1>bound
  <2> QED BY <2>1, <2>2, <2>3
<1>rangefin. IsFiniteSet(0..(Cardinality(Acceptors)+1))  BY <1>Nnat, FS_Interval
<1>Lfin. IsFiniteSet(L)  BY <1>Lsub, <1>rangefin, FS_Subset
<1>lIn. Len(l) \in L  OBVIOUS
<1>Lne. L # {}  BY <1>lIn
<1>Lnat. \A x \in L : x \in Nat  BY <1>Lsub
<1>maxprops. Max(L) \in L /\ (\A y \in L : Max(L) >= y)  BY <1>Lfin, <1>Lne, <1>Lnat, MaxProps
<1>MaxLnat. Max(L) \in Nat  BY <1>maxprops, <1>Lsub
<1>d_witness. Max(L) - 1 \in D  BY <1>maxprops
<1>d_upper. \A d \in D : d <= Max(L) - 1
  <2> SUFFICES ASSUME NEW d \in D PROVE d <= Max(L) - 1  OBVIOUS
  <2>1. PICK s \in ValidSeqs(alpha) : d = Len(s) - 1  OBVIOUS
  <2>2. Len(s) \in L  BY <2>1
  <2>3. Len(s) <= Max(L)  BY <2>2, <1>maxprops
  <2>4. Len(s) \in Nat  BY <2>1 DEF ValidSeqs
  <2> QED BY <2>1, <2>3, <2>4, <1>MaxLnat
<1>witness2. \E x \in D : \A y \in D : x >= y
  BY <1>d_witness, <1>d_upper
<1>maxprops2. MaxDepth(alpha) \in D /\ (\A y \in D : MaxDepth(alpha) >= y)
  BY <1>witness2 DEF MaxDepth, Max
<1>lIn2. Len(l) - 1 \in D  OBVIOUS
<1> QED BY <1>maxprops2, <1>lIn2

\* --- message-structure facts ---------------------------------------

\* TranClosure is Tran-closed and stays inside Messages.
LEMMA TranClosureClosed ==
  ASSUME TypeOKMessageInterface, TranTrans,
         NEW mset \in SUBSET Messages, NEW x \in TranClosure(mset)
  PROVE x \in Messages /\ Tran(x) \subseteq TranClosure(mset)
<1>1. PICK y \in mset : x \in Tran(y)  BY DEF TranClosure
<1>2. y \in Messages  BY <1>1
<1>3. x \in Messages  BY <1>1, <1>2, TranSubMessages
<1>4. Tran(x) \subseteq Tran(y)  BY <1>1, <1>2 DEF TranTrans
<1>5. Tran(y) \subseteq TranClosure(mset)  BY <1>1 DEF TranClosure
<1> QED BY <1>3, <1>4, <1>5

\* Ballots never increase along Tran: an ancestor's proposals are among the
\* descendant's proposals.
LEMMA BMonotone ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, AlwaysAProposal,
         NEW x \in Messages, NEW y \in Tran(x)
  PROVE B(y) <= B(x)
<1>finX. IsFiniteSet(GetProposals(x))
  <2>1. GetProposals(x) \subseteq Tran(x)  BY DEF GetProposals
  <2>2. IsFiniteSet(Tran(x))  BY DEF TranFinite
  <2> QED BY <2>1, <2>2, FS_Subset
<1>subX. GetProposals(x) \subseteq Proposals  BY DEF GetProposals
<1>neX. GetProposals(x) # {}  BY DEF AlwaysAProposal
<1>Xchoose. /\ B(x) \in {ProposalBal(z) : z \in GetProposals(x)}
            /\ \A w \in {ProposalBal(z) : z \in GetProposals(x)} : B(x) >= w
  BY <1>finX, <1>subX, <1>neX, MaxBSetProperty DEF B
<1>yM. y \in Messages  BY TranSubMessages
<1>subT. Tran(y) \subseteq Tran(x)  BY DEF TranTrans
<1>subGP. GetProposals(y) \subseteq GetProposals(x)  BY <1>subT DEF GetProposals
<1>finY. IsFiniteSet(GetProposals(y))
  <2>1. GetProposals(y) \subseteq Tran(y)  BY DEF GetProposals
  <2>2. IsFiniteSet(Tran(y))  BY <1>yM DEF TranFinite
  <2> QED BY <2>1, <2>2, FS_Subset
<1>subY. GetProposals(y) \subseteq Proposals  BY DEF GetProposals
<1>neY. GetProposals(y) # {}  BY <1>yM DEF AlwaysAProposal
<1>Ychoose. /\ B(y) \in {ProposalBal(z) : z \in GetProposals(y)}
            /\ \A w \in {ProposalBal(z) : z \in GetProposals(y)} : B(y) >= w
  BY <1>finY, <1>subY, <1>neY, MaxBSetProperty DEF B
<1>1. B(y) \in {ProposalBal(z) : z \in GetProposals(x)}
  <2>1. PICK zz \in GetProposals(y) : B(y) = ProposalBal(zz)  BY <1>Ychoose
  <2>2. zz \in GetProposals(x)  BY <2>1, <1>subGP
  <2> QED BY <2>1, <2>2
<1> QED BY <1>1, <1>Xchoose

\* Catching is monotone along Tran: an ancestor's evidence is a subset of
\* the descendant's evidence.
LEMMA CaughtMonotoneTran ==
  ASSUME TypeOKMessageInterface, TranTrans,
         NEW x \in Messages, NEW y \in Tran(x)
  PROVE Caught(y) \subseteq Caught(x)
<1>sub. Tran(y) \subseteq Tran(x)  BY DEF TranTrans
<1> SUFFICES ASSUME NEW a \in Caught(y) PROVE a \in Caught(x)  OBVIOUS
<1>1. PICK m1 \in Tran(y), m2 \in Tran(y) :
        Sig(m1)=a /\ Sig(m2)=a /\ m1 \notin Tran(m2) /\ m2 \notin Tran(m1)
  BY DEF Caught, CaughtS
<1>2. m1 \in Tran(x) /\ m2 \in Tran(x)  BY <1>1, <1>sub
<1>3. a \in Acceptors  BY DEF Caught, CaughtS
<1> QED BY <1>1, <1>2, <1>3 DEF Caught, CaughtS

\* Hence connectivity only grows when walking to an ancestor.
LEMMA ConMonotoneTran ==
  ASSUME TypeOKMessageInterface, TranTrans, NEW alpha \in Learners,
         NEW x \in Messages, NEW y \in Tran(x)
  PROVE Con(alpha, x) \subseteq Con(alpha, y)
<1>1. Caught(y) \subseteq Caught(x)  BY CaughtMonotoneTran
<1>2. ConFromCaught(alpha, Caught(x)) \subseteq ConFromCaught(alpha, Caught(y))
  BY <1>1, ConFromCaughtAntitone
<1> QED BY <1>2 DEF Con

\* Everything caught as of a closure member is caught as of the closure.
LEMMA CaughtSubClosure ==
  ASSUME TypeOKMessageInterface, TranTrans,
         NEW mset \in SUBSET Messages, NEW x \in TranClosure(mset)
  PROVE Caught(x) \subseteq CaughtS(TranClosure(mset))
<1>sub. Tran(x) \subseteq TranClosure(mset)  BY TranClosureClosed
<1> SUFFICES ASSUME NEW a \in Caught(x) PROVE a \in CaughtS(TranClosure(mset))  OBVIOUS
<1>1. PICK m1 \in Tran(x), m2 \in Tran(x) :
        Sig(m1)=a /\ Sig(m2)=a /\ m1 \notin Tran(m2) /\ m2 \notin Tran(m1)
  BY DEF Caught, CaughtS
<1>2. m1 \in TranClosure(mset) /\ m2 \in TranClosure(mset)  BY <1>1, <1>sub
<1>3. a \in Acceptors  BY DEF Caught, CaughtS
<1> QED BY <1>1, <1>2, <1>3 DEF CaughtS

\* An acceptor not caught in a message set has Tran-comparable messages
\* there (immediate from the definition of CaughtS).
LEMMA UncaughtSameSigComparable ==
  ASSUME NEW M, NEW a \in Acceptors, a \notin CaughtS(M),
         NEW x \in M, NEW y \in M, Sig(x) = a, Sig(y) = a
  PROVE x \in Tran(y) \/ y \in Tran(x)
<1> SUFFICES ASSUME x \notin Tran(y), y \notin Tran(x) PROVE FALSE  OBVIOUS
<1>1. a \in CaughtS(M)  BY DEF CaughtS
<1> QED BY <1>1

\* Any nonempty message set has a ballot-minimal element (ballots are
\* naturals) -- used to realize TraceCondCoreMin.
LEMMA ExistsMinBallotElement ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, AlwaysAProposal,
         NEW S \in SUBSET Messages, S # {}
  PROVE \E x \in S : \A y \in S : B(x) <= B(y)
<1> DEFINE Q(n) == \A T \in SUBSET Messages : (\E t \in T : B(t) = n)
                     => (\E x \in T : \A y \in T : B(x) <= B(y))
<1> SUFFICES \A n \in Nat : Q(n)
  <2>1. PICK s0 \in S : TRUE  OBVIOUS
  <2>2. s0 \in Messages  BY <2>1
  <2>3. B(s0) \in Ballots  BY <2>2, BBallot
  <2>4. B(s0) \in Nat  BY <2>3 DEF Ballots
  <2>5. \E t \in S : B(t) = B(s0)  BY <2>1
  <2> QED BY <2>4, <2>5 DEF Q
<1> HIDE DEF Q
<1>ind. \A n \in Nat : (\A k \in 0..(n-1) : Q(k)) => Q(n)
  <2> USE DEF Q
  <2> SUFFICES ASSUME NEW n \in Nat, \A k \in 0..(n-1) : Q(k),
                      NEW T \in SUBSET Messages, NEW t \in T, B(t) = n
               PROVE \E x \in T : \A y \in T : B(x) <= B(y)
    OBVIOUS
  <2> DEFINE T2 == {y \in T : B(y) < n}
  <2>1. CASE T2 = {}
    <3>1. \A y \in T : B(y) >= n
      <4> SUFFICES ASSUME NEW y \in T PROVE B(y) >= n  OBVIOUS
      <4>yM. y \in Messages  OBVIOUS
      <4>yB. B(y) \in Ballots  BY <4>yM, BBallot
      <4>yNat. B(y) \in Nat  BY <4>yB DEF Ballots
      <4> QED BY <2>1, <4>yNat
    <3> QED BY <3>1
  <2>2. CASE T2 # {}
    <3>t2. PICK t2 \in T2 : TRUE  BY <2>2
    <3>t2T. t2 \in T /\ B(t2) < n  BY <3>t2
    <3>t2M. t2 \in Messages  BY <3>t2T
    <3>t2B. B(t2) \in Ballots  BY <3>t2M, BBallot
    <3>t2Nat. B(t2) \in Nat  BY <3>t2B DEF Ballots
    <3>k. B(t2) \in 0..(n-1)  BY <3>t2T, <3>t2Nat
    <3>Qk. \A k \in 0..(n-1) : Q(k)  OBVIOUS
    <3>Qbt2. Q(B(t2))  BY <3>k, <3>Qk
    <3>wit. \E tt \in T : B(tt) = B(t2)  BY <3>t2T
    <3> QED BY <3>Qbt2, <3>wit DEF Q
  <2> QED BY <2>1, <2>2
<1> QED BY <1>ind, GeneralNatInduction, IsaM("blast")

\* Generic min-existence for Cardinality(Tran(.)) over a possibly-unbounded
\* message set (Nat well-ordering, no finiteness of S needed) -- the "swap
\* B for TranCard" twin of ExistsMinBallotElement above, used to realize
\* TraceCondCoreMin's minimality (item 15) via the Tran-DAG-depth measure
\* (ballots legitimately repeat within one TwoA's depth-tree, so they can't
\* serve as the well-founded measure there -- see TraceCondCore's item 3).
LEMMA ExistsMinTranCardElement ==
  ASSUME TranFinite,
         NEW S \in SUBSET Messages, S # {}
  PROVE \E x \in S : \A y \in S : TranCard(x) <= TranCard(y)
<1> DEFINE Q(n) == \A T \in SUBSET Messages : (\E t \in T : TranCard(t) = n)
                     => (\E x \in T : \A y \in T : TranCard(x) <= TranCard(y))
<1> SUFFICES \A n \in Nat : Q(n)
  <2>1. PICK s0 \in S : TRUE  OBVIOUS
  <2>2. s0 \in Messages  BY <2>1
  <2>3. TranCard(s0) \in Nat  BY <2>2, TranCardNat DEF TranCard
  <2>5. \E t \in S : TranCard(t) = TranCard(s0)  BY <2>1
  <2> QED BY <2>3, <2>5 DEF Q
<1> HIDE DEF Q
<1>ind. \A n \in Nat : (\A k \in 0..(n-1) : Q(k)) => Q(n)
  <2> USE DEF Q
  <2> SUFFICES ASSUME NEW n \in Nat, \A k \in 0..(n-1) : Q(k),
                      NEW T \in SUBSET Messages, NEW t \in T, TranCard(t) = n
               PROVE \E x \in T : \A y \in T : TranCard(x) <= TranCard(y)
    OBVIOUS
  <2> DEFINE T2 == {y \in T : TranCard(y) < n}
  <2>1. CASE T2 = {}
    <3>1. \A y \in T : TranCard(y) >= n
      <4> SUFFICES ASSUME NEW y \in T PROVE TranCard(y) >= n  OBVIOUS
      <4>yM. y \in Messages  OBVIOUS
      <4>yNat. TranCard(y) \in Nat  BY <4>yM, TranCardNat DEF TranCard
      <4> QED BY <2>1, <4>yNat
    <3> QED BY <3>1
  <2>2. CASE T2 # {}
    <3>t2. PICK t2 \in T2 : TRUE  BY <2>2
    <3>t2T. t2 \in T /\ TranCard(t2) < n  BY <3>t2
    <3>t2M. t2 \in Messages  BY <3>t2T
    <3>t2Nat. TranCard(t2) \in Nat  BY <3>t2M, TranCardNat DEF TranCard
    <3>k. TranCard(t2) \in 0..(n-1)  BY <3>t2T, <3>t2Nat
    <3>Qk. \A k \in 0..(n-1) : Q(k)  OBVIOUS
    <3>Qbt2. Q(TranCard(t2))  BY <3>k, <3>Qk
    <3>wit. \E tt \in T : TranCard(tt) = TranCard(t2)  BY <3>t2T
    <3> QED BY <3>Qbt2, <3>wit DEF Q
  <2> QED BY <2>1, <2>2
<1> QED BY <1>ind, GeneralNatInduction, IsaM("blast")

\* Any nonempty set of naturals has a least element -- used to pick the
\* EARLIEST chain index at which a learner is connected (the k* of
\* hpaxos-tla's HeterogeneousTraceExistence <4>6), which is what breaks the
\* item-6 circularity: substituting a candidate at index k*+1 makes item 5
\* the definition of k* and item 6 its minimality.
LEMMA ExistsLeastIndex ==
  ASSUME NEW S \in SUBSET Nat, S # {}
  PROVE \E i \in S : \A j \in S : i <= j
<1> DEFINE Q(n) == \A T \in SUBSET Nat : n \in T => \E i \in T : \A j \in T : i <= j
<1> SUFFICES \A n \in Nat : Q(n)
  <2>1. PICK s0 \in S : TRUE  OBVIOUS
  <2>2. s0 \in Nat  OBVIOUS
  <2> QED BY <2>1, <2>2 DEF Q
<1> HIDE DEF Q
<1>ind. \A n \in Nat : (\A k \in 0..(n-1) : Q(k)) => Q(n)
  <2> USE DEF Q
  <2> SUFFICES ASSUME NEW n \in Nat, \A k \in 0..(n-1) : Q(k),
                      NEW T \in SUBSET Nat, n \in T
               PROVE \E i \in T : \A j \in T : i <= j
    OBVIOUS
  <2> DEFINE T2 == {j \in T : j < n}
  <2>1. CASE T2 = {}
    <3>1. \A j \in T : n <= j
      <4> SUFFICES ASSUME NEW j \in T PROVE n <= j  OBVIOUS
      <4>1. j \in Nat  OBVIOUS
      <4> QED BY <2>1, <4>1
    <3> QED BY <3>1
  <2>2. CASE T2 # {}
    <3>1. PICK t2 \in T2 : TRUE  BY <2>2
    <3>2. t2 \in T /\ t2 < n /\ t2 \in Nat  BY <3>1
    <3>3. t2 \in 0..(n-1)  BY <3>2
    <3>4. Q(t2)  BY <3>3
    <3> QED BY <3>4, <3>2
  <2> QED BY <2>1, <2>2
<1> QED BY <1>ind, GeneralNatInduction, IsaM("blast")

\* --- depth machinery -----------------------------------------------

\* Quorums are upward-closed within finite subsets of Acceptors (abstract
\* analogue of MessageConcrete's CQuorumUpward -- same proof, since Quorums
\* is the same LearnerGraphInterface operator in both worlds).
LEMMA QuorumUpward ==
  ASSUME NEW l \in Learners, NEW s, NEW t,
         s \in Quorums(l), s \subseteq t, t \subseteq Acceptors, IsFiniteSet(t)
  PROVE t \in Quorums(l)
<1>1. \E mm \in GetSpecifiedQuorums(l) : mm \subseteq s  BY DEF Quorums
<1>2. \E mm \in GetSpecifiedQuorums(l) : mm \subseteq t  BY <1>1
<1> QED BY <1>2 DEF Quorums

\* What membership in Qd gives you (DEF Qd plus HasDepth's own signature
\* requirement).
LEMMA QdProperties ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         NEW alpha \in Learners, NEW x \in Messages,
         NEW d \in Nat, d >= 1,
         NEW y \in Qd(alpha, x, d)
  PROVE /\ y \in TranExclusive(x)
        /\ B(y) = B(x)
        /\ Sig(y) \in Acceptors
        /\ HasDepth(alpha, y, d - 1)
<1>1. y \in TranExclusive(x) /\ B(x) = B(y) /\ HasDepth(alpha, y, d-1)  BY DEF Qd
<1>2. Sig(y) \in Acceptors  BY <1>1 DEF HasDepth
<1> QED BY <1>1, <1>2

\* Qd membership yields depth at ANY index e explicitly equated to d - 1.
\* The explicit e parameter makes the goal-side match first-order: backends
\* abstract compound arithmetic inside opaque applications, so asking them
\* to recognize HasDepth(_, _, D - k + 1 - 1) as the instance of
\* HasDepth(_, _, d - 1) at d := D - k + 1 fails, while matching a plain
\* parameter e and separately discharging e = d - 1 (reflexive at the call
\* site) succeeds.
LEMMA QdDepthMember ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         NEW alpha \in Learners, NEW x \in Messages,
         NEW d \in Nat, d >= 1,
         NEW y \in Qd(alpha, x, d),
         NEW e, e = d - 1
  PROVE HasDepth(alpha, y, e)
<1>1. HasDepth(alpha, y, d - 1)  BY DEF Qd
<1> QED BY <1>1

\* Depth-1 quorum members are fresh OneBs (HasDepthDef at d = 0).
LEMMA QdOneBFresh ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         NEW alpha \in Learners, NEW x \in Messages,
         NEW y \in Qd(alpha, x, 1)
  PROVE IsOneB(y) /\ Fresh(alpha, y) /\ Sig(y) \in Acceptors
<1>1. y \in TranExclusive(x) /\ B(x) = B(y) /\ HasDepth(alpha, y, 0)  BY DEF Qd
<1>yM. y \in Messages
  <2>1. y \in Tran(x)  BY <1>1 DEF TranExclusive
  <2> QED BY <2>1, TranSubMessages
<1>z. 0 \in Nat  OBVIOUS
<1>2. HasDepth(alpha, y, 0) =
        (/\ Sig(y) \in Acceptors
         /\ IF 0 = 0 THEN (IsOneB(y) /\ Fresh(alpha, y))
                     ELSE SigS(Qd(alpha, y, 0)) \in Quorums(alpha))
  BY <1>yM, <1>z, HasDepthDef
<1> QED BY <1>1, <1>2

\* Depth is downward closed above 1: a depth-d quorum's members supply the
\* depth-e quorums for every 1 <= e <= d, since Qd sets nest (via TranTrans)
\* and Quorums are upward closed.  (Abstract analogue of MessageConcrete's
\* CDepthDownward; does NOT extend to e = 0.)
LEMMA HasDepthDownward ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         LearnersMightAgree, ValidLearnerGraphAssumption,
         NEW alpha \in Learners, NEW x \in Messages,
         NEW d \in Nat, NEW e \in Nat,
         1 <= e, e <= d,
         HasDepth(alpha, x, d)
  PROVE HasDepth(alpha, x, e)
<1> DEFINE W(n) == {p \in TranExclusive(x) : B(p) = B(x) /\ HasDepth(alpha, p, n)}
<1> DEFINE Q(n) == SigS(W(n)) \in Quorums(alpha) => \A i \in 0..n : SigS(W(i)) \in Quorums(alpha)
<1>xSig. Sig(x) \in Acceptors  BY DEF HasDepth
<1>dpos. d >= 1  OBVIOUS
<1>epos. e >= 1  OBVIOUS
<1>dnat. d - 1 \in Nat  BY <1>dpos
<1>enat. e - 1 \in Nat  BY <1>epos
<1>drange. e - 1 \in 0..(d-1)  BY <1>dpos, <1>epos
<1>Wd1eq. W(d-1) = Qd(alpha, x, d)  BY <1>dpos DEF Qd
<1>We1eq. W(e-1) = Qd(alpha, x, e)  BY <1>epos DEF Qd
<1>hdd. Sig(x) \in Acceptors /\ SigS(Qd(alpha, x, d)) \in Quorums(alpha)
  <2>1. d # 0  BY <1>dpos
  <2>2. HasDepth(alpha, x, d) =
          (/\ Sig(x) \in Acceptors
           /\ IF d = 0 THEN (IsOneB(x) /\ Fresh(alpha, x))
                       ELSE SigS(Qd(alpha, x, d)) \in Quorums(alpha))
    BY HasDepthDef
  <2> QED BY <2>1, <2>2
<1>base. SigS(W(d-1)) \in Quorums(alpha)  BY <1>hdd, <1>Wd1eq
<1> SUFFICES \A n \in Nat : Q(n)
  <2>1. Q(d-1)  BY <1>dnat
  <2>2. \A i \in 0..(d-1) : SigS(W(i)) \in Quorums(alpha)  BY <2>1, <1>base DEF Q
  <2>3. SigS(W(e-1)) \in Quorums(alpha)  BY <2>2, <1>drange
  <2>4. SigS(Qd(alpha, x, e)) \in Quorums(alpha)  BY <2>3, <1>We1eq
  <2>5. e # 0  BY <1>epos
  <2>6. HasDepth(alpha, x, e) =
          (/\ Sig(x) \in Acceptors
           /\ IF e = 0 THEN (IsOneB(x) /\ Fresh(alpha, x))
                       ELSE SigS(Qd(alpha, x, e)) \in Quorums(alpha))
    BY HasDepthDef
  <2> QED BY <2>4, <1>xSig, <2>5, <2>6
<1> HIDE DEF Q
<1>ind. \A n \in Nat : (\A kk \in 0..(n-1) : Q(kk)) => Q(n)
  <2> USE DEF Q
  <2> SUFFICES ASSUME NEW n \in Nat, \A kk \in 0..(n-1) : Q(kk),
                      SigS(W(n)) \in Quorums(alpha)
               PROVE \A i \in 0..n : SigS(W(i)) \in Quorums(alpha)
    OBVIOUS
  <2>1. CASE n = 0
    <3> SUFFICES ASSUME NEW i \in 0..n PROVE SigS(W(i)) \in Quorums(alpha)  OBVIOUS
    <3>1. i = 0  BY <2>1
    <3> QED BY <3>1, <2>1
  <2>2. CASE n >= 1
    <3>nn. n \in Nat /\ n >= 1  BY <2>2
    <3>step. SigS(W(n-1)) \in Quorums(alpha)
      <4>ne. W(n) # {}
        <5>1. SigS(W(n)) # {}  BY QuorumsHaveMembers
        <5> QED BY <5>1 DEF SigS
      <4>p. PICK p \in W(n) : TRUE  BY <4>ne
      <4>pW. p \in TranExclusive(x) /\ B(p) = B(x) /\ HasDepth(alpha, p, n)  BY <4>p
      <4>pTran. p \in Tran(x) /\ p # x  BY <4>pW DEF TranExclusive
      <4>pMsg. p \in Messages  BY <4>pTran, TranSubMessages
      <4>hd. HasDepth(alpha, p, n) =
               (Sig(p) \in Acceptors /\ SigS(Qd(alpha, p, n)) \in Quorums(alpha))
        <5>1. n # 0  BY <3>nn
        <5>2. HasDepth(alpha, p, n) =
                (/\ Sig(p) \in Acceptors
                 /\ IF n = 0 THEN (IsOneB(p) /\ Fresh(alpha, p))
                             ELSE SigS(Qd(alpha, p, n)) \in Quorums(alpha))
          BY <4>pMsg, HasDepthDef
        <5> QED BY <5>1, <5>2
      <4>quo. SigS(Qd(alpha, p, n)) \in Quorums(alpha)  BY <4>hd, <4>pW
      <4>qd. Qd(alpha, p, n) = {q \in TranExclusive(p) : B(p) = B(q) /\ HasDepth(alpha, q, n-1)}
        BY <3>nn DEF Qd
      <4>sub. Qd(alpha, p, n) \subseteq W(n-1)
        <5> SUFFICES ASSUME NEW q \in Qd(alpha, p, n) PROVE q \in W(n-1)  OBVIOUS
        <5>1. q \in TranExclusive(p) /\ B(p) = B(q) /\ HasDepth(alpha, q, n-1)  BY <4>qd
        <5>2. q \in Tran(p) /\ q # p  BY <5>1 DEF TranExclusive
        <5>3. Tran(p) \subseteq Tran(x)  BY <4>pTran, <4>pMsg DEF TranTrans
        <5>4. q \in Tran(x)  BY <5>2, <5>3
        <5>qnex. q # x
          <6> SUFFICES ASSUME q = x PROVE FALSE  OBVIOUS
          <6>1. x \in Tran(p)  BY <5>2
          <6>2. p \in Tran(x)  BY <4>pTran
          <6>3. p = x  BY <6>1, <6>2, <4>pMsg, TranAntisym
          <6> QED BY <6>3, <4>pTran
        <5>5. q \in TranExclusive(x)  BY <5>4, <5>qnex DEF TranExclusive
        <5>6. B(q) = B(x)  BY <5>1, <4>pW
        <5> QED BY <5>5, <5>6, <5>1
      <4>sigsub. SigS(Qd(alpha, p, n)) \subseteq SigS(W(n-1))  BY <4>sub DEF SigS
      <4>fin. IsFiniteSet(W(n-1))
        <5>1. W(n-1) \subseteq Tran(x)  BY DEF TranExclusive
        <5>2. IsFiniteSet(Tran(x))  BY DEF TranFinite
        <5> QED BY <5>1, <5>2, FS_Subset
      <4>finsig. IsFiniteSet(SigS(W(n-1)))  BY <4>fin, FS_Image DEF SigS
      <4>acc. SigS(W(n-1)) \subseteq Acceptors
        <5> SUFFICES ASSUME NEW aa \in SigS(W(n-1)) PROVE aa \in Acceptors  OBVIOUS
        <5>1. PICK q \in W(n-1) : aa = Sig(q)  BY DEF SigS
        <5>2. HasDepth(alpha, q, n-1)  BY <5>1
        <5>3. Sig(q) \in Acceptors  BY <5>2 DEF HasDepth
        <5> QED BY <5>1, <5>3
      <4> QED BY <4>quo, <4>sigsub, <4>acc, <4>finsig, QuorumUpward
    <3>n1. n-1 \in 0..(n-1)  BY <3>nn
    <3>Qn1. Q(n-1)  BY <3>n1
    <3>below. \A i \in 0..(n-1) : SigS(W(i)) \in Quorums(alpha)  BY <3>Qn1, <3>step
    <3> SUFFICES ASSUME NEW i \in 0..n PROVE SigS(W(i)) \in Quorums(alpha)  OBVIOUS
    <3>a. CASE i = n  BY <3>a
    <3>b. CASE i \in 0..(n-1)  BY <3>b, <3>below
    <3> QED BY <2>2, <3>a, <3>b
  <2> QED BY <2>1, <2>2
<1> QED BY <1>ind, GeneralNatInduction, IsaM("blast")

\* Any positive depth registers the learner in Lrns.
LEMMA HasDepthLrns ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         LearnersMightAgree, ValidLearnerGraphAssumption,
         NEW alpha \in Learners, NEW x \in Messages,
         NEW d \in Nat, d >= 1,
         HasDepth(alpha, x, d)
  PROVE alpha \in Lrns(x)
<1>1. HasDepth(alpha, x, 1)  BY HasDepthDownward
<1> QED BY <1>1 DEF Lrns

\* --- freshness extraction ------------------------------------------

\* A finite nonempty message set has a B-maximal element.  First-order
\* wrapper around FiniteMaxExists (which TLAPS cannot apply directly to a
\* locally-DEFINEd set; same pattern as TranMaxExists).
LEMMA BMaxExists ==
  ASSUME TypeOKMessageInterface, TranFinite, AlwaysAProposal,
         NEW T, IsFiniteSet(T), T # {}, T \subseteq Messages
  PROVE \E r \in T : \A y \in T : B(y) <= B(r)
<1>1. \A z \in T : B(z) \in Nat
  <2> SUFFICES ASSUME NEW z \in T PROVE B(z) \in Nat  OBVIOUS
  <2>1. z \in Messages  OBVIOUS
  <2>2. B(z) \in Ballots  BY <2>1, BBallot
  <2> QED BY <2>2 DEF Ballots
<1> QED BY <1>1, FiniteMaxExists

\* The engine of the chain step (paper Definition 17 used at the top
\* ballot): if a fresh message r references a value-disagreeing message w
\* that carries a connected learner, then r references a strictly
\* higher-ballot message p that ALSO carries a connected learner and agrees
\* with r's value.  (Take p ballot-maximal among connected-learner-bearing
\* members of Tran(r): Fresh's second disjunct fails for it by choice, its
\* third by maximality, leaving value agreement.)
LEMMA FreshTopConnected ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         AlwaysAProposal,
         NEW gamma \in Learners, NEW r \in Messages,
         Fresh(gamma, r),
         NEW w \in Tran(r),
         V(w) # V(r),
         Con(gamma, r) \cap Lrns(w) # {}
  PROVE \E p \in Tran(r) :
          /\ B(p) > B(w)
          /\ V(p) = V(r)
          /\ Con(gamma, r) \cap Lrns(p) # {}
<1> DEFINE CandSet == {z \in Tran(r) : Con(gamma, r) \cap Lrns(z) # {}}
<1>wCand. w \in CandSet  OBVIOUS
<1>ne. CandSet # {}  BY <1>wCand
<1>finTr. IsFiniteSet(Tran(r))  BY DEF TranFinite
<1>fin. IsFiniteSet(CandSet)  BY <1>finTr, FS_Subset
<1>candM. CandSet \subseteq Messages
  <2> SUFFICES ASSUME NEW z \in CandSet PROVE z \in Messages  OBVIOUS
  <2>0. z \in Tran(r)  OBVIOUS
  <2> QED BY <2>0, TranSubMessages
<1>Bnat. \A z \in CandSet : B(z) \in Nat
  <2> SUFFICES ASSUME NEW z \in CandSet PROVE B(z) \in Nat  OBVIOUS
  <2>1. z \in Messages  BY <1>candM
  <2>2. B(z) \in Ballots  BY <2>1, BBallot
  <2> QED BY <2>2 DEF Ballots
<1>max. \E pp \in CandSet : \A y \in CandSet : B(y) <= B(pp)
  BY <1>fin, <1>ne, <1>candM, BMaxExists
<1> PICK p \in CandSet : \A y \in CandSet : B(y) <= B(p)  BY <1>max
<1>pR. p \in Tran(r)  OBVIOUS
<1>pCon. Con(gamma, r) \cap Lrns(p) # {}  OBVIOUS
<1>pMax. \A y \in CandSet : B(y) <= B(p)  OBVIOUS
\* p cannot be improved: applying Fresh at p rules out disjuncts 2 and 3
<1>notThird. \A pp \in TranExclusive(r) : ~(B(pp) > B(p) /\ Con(gamma, r) \cap Lrns(pp) # {})
  <2> SUFFICES ASSUME NEW pp \in TranExclusive(r), B(pp) > B(p), Con(gamma,r) \cap Lrns(pp) # {}
               PROVE FALSE
    OBVIOUS
  <2>1. pp \in Tran(r)  BY DEF TranExclusive
  <2>2. pp \in CandSet  BY <2>1
  <2>3. B(pp) <= B(p)  BY <2>2, <1>pMax
  <2>ty. B(pp) \in Nat /\ B(p) \in Nat  BY <1>Bnat, <2>2
  <2> QED BY <2>3, <2>ty
<1>freshP. \/ V(p) = V(r) \/ Con(gamma,r) \cap Lrns(p) = {}
           \/ \E pp \in TranExclusive(r): B(pp) > B(p) /\ Con(gamma,r) \cap Lrns(pp) # {}
  BY <1>pR DEF Fresh
<1>Veq. V(p) = V(r)  BY <1>freshP, <1>pCon, <1>notThird
\* separately: Fresh applied at w forces a strictly-higher candidate, so
\* p (the max) strictly beats w
<1>freshW. \/ V(w) = V(r) \/ Con(gamma,r) \cap Lrns(w) = {}
           \/ \E pp \in TranExclusive(r): B(pp) > B(w) /\ Con(gamma,r) \cap Lrns(pp) # {}
  BY DEF Fresh
<1>witPw. \E pp \in TranExclusive(r): B(pp) > B(w) /\ Con(gamma,r) \cap Lrns(pp) # {}
  BY <1>freshW
<1> PICK pw \in TranExclusive(r) : B(pw) > B(w) /\ Con(gamma,r) \cap Lrns(pw) # {}  BY <1>witPw
<1>pwR. pw \in Tran(r)  BY DEF TranExclusive
<1>pwCand. pw \in CandSet  BY <1>pwR
<1>pwLe. B(pw) <= B(p)  BY <1>pwCand, <1>pMax
<1>strict. B(p) > B(w)
  <2>ty. B(p) \in Nat /\ B(pw) \in Nat /\ B(w) \in Nat  BY <1>Bnat, <1>wCand, <1>pwCand
  <2> QED BY <1>pwLe, <2>ty
<1> QED BY <1>pR, <1>strict, <1>Veq, <1>pCon

\* --- decision witnesses --------------------------------------------

\* Every decision (slow or fast) exhibits a closure message at the decision
\* ballot attested by the deciding learner: via any member of the slow
\* decision's nonempty MaxDepth quorum (HasDepthDownward + HasDepthLrns).
LEMMA DecisionHighWitness ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions,
         NEW mset \in SUBSET Messages,
         NEW beta \in Learners, NEW b \in Ballots,
         Decision(mset, beta, b)
  PROVE \E M \in TranClosure(mset) : B(M) = b /\ beta \in Lrns(M)
<1>mi. TypeOKMessageInterface /\ TranFinite /\ TranTrans /\ TranAcyclic /\ AlwaysAProposal
  BY DEF MessageInterfaceAssumptions
<1>lga. FiniteAcceptors /\ LearnersNonEmpty /\ QuorumsNonEmpty /\ LearnersMightAgree /\ ValidLearnerGraphAssumption
  BY DEF LearnerGraphAssumptions
<1>1. CASE DecisionSlow(mset, beta, b)
  <2> DEFINE W == {x \in TranClosure(mset) : B(x) = b /\ HasDepth(beta, x, MaxDepth(beta))}
  <2>sigs. SigS(W) \in Quorums(beta)  BY <1>1 DEF DecisionSlow
  <2>ne. SigS(W) # {}  BY <2>sigs, <1>lga, QuorumsHaveMembers
  <2>Wne. W # {}  BY <2>ne DEF SigS
  <2> PICK M \in W : TRUE  BY <2>Wne
  <2>M. M \in TranClosure(mset) /\ B(M) = b /\ HasDepth(beta, M, MaxDepth(beta))  OBVIOUS
  <2>MMsg. M \in Messages  BY <2>M, <1>mi, TranClosureClosed
  <2>mdpos. MaxDepth(beta) \in 1..Cardinality(Acceptors)  BY <1>lga, MaxDepthFiniteAcceptors
  <2>mdge1. MaxDepth(beta) >= 1 /\ MaxDepth(beta) \in Nat  BY <2>mdpos
  <2>lrn. beta \in Lrns(M)  BY <2>M, <2>MMsg, <2>mdge1, <1>mi, <1>lga, HasDepthLrns
  <2> QED BY <2>M, <2>lrn
<1> QED BY <1>1 DEF Decision

\* --- the trace: properties, existence, contradiction ---------------

\* Structural consequences of the core conditions (hpaxos-tla
\* HeterogeneousSpecCondProperties): the chain lives in the closure, the
\* rr_x descend along Tran, and their connectivity sets strictly grow
\* (item 5 supplies growth witnesses one index ahead, hence j < K).
LEMMA TraceCoreProperties ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions,
         NEW mset \in SUBSET Messages,
         NEW alpha \in Learners, NEW lobal \in Ballots,
         NEW himsg \in TranClosure(mset),
         NEW K \in Nat,
         NEW seq \in [1..K -> TraceElem],
         \A x \in 1..K : TraceCondCore(alpha, lobal, TranClosure(mset), himsg, seq, x)
  PROVE /\ \A i \in 1..K : /\ seq[i].mm \in TranClosure(mset)
                           /\ seq[i].rr \in TranClosure(mset)
                           /\ seq[i].ss \in TranClosure(mset)
        /\ \A i, j \in 1..K : i < j => seq[j].rr \in Tran(seq[i].rr)
        /\ \A i, j \in 1..K : (i < j /\ j < K) =>
             /\ Con(alpha, seq[i].rr) \subseteq Con(alpha, seq[j].rr)
             /\ Con(alpha, seq[i].rr) # Con(alpha, seq[j].rr)
<1>mi. TypeOKMessageInterface /\ TranFinite /\ TranTrans /\ TranAcyclic /\ AlwaysAProposal
  BY DEF MessageInterfaceAssumptions
<1>hmMsg. himsg \in Messages /\ Tran(himsg) \subseteq TranClosure(mset)  BY <1>mi, TranClosureClosed
<1>elt. \A i \in 1..K :
          /\ seq[i].mm \in TranClosure(mset)
          /\ seq[i].rr \in TranClosure(mset)
          /\ seq[i].ss \in TranClosure(mset)
  <2> SUFFICES ASSUME NEW i \in 1..K
               PROVE /\ seq[i].mm \in TranClosure(mset)
                     /\ seq[i].rr \in TranClosure(mset)
                     /\ seq[i].ss \in TranClosure(mset)
    OBVIOUS
  <2>cc. TraceCondCore(alpha, lobal, TranClosure(mset), himsg, seq, i)  OBVIOUS
  <2>mm. seq[i].mm \in Tran(himsg)  BY <2>cc DEF TraceCondCore
  <2>mmTC. seq[i].mm \in TranClosure(mset)  BY <2>mm, <1>hmMsg
  <2>mmMsg. seq[i].mm \in Messages /\ Tran(seq[i].mm) \subseteq TranClosure(mset)
    BY <2>mmTC, <1>mi, TranClosureClosed
  <2>rr. seq[i].rr \in Qd(seq[i].gamma, seq[i].mm, 1)  BY <2>cc DEF TraceCondCore
  <2>rrTE. seq[i].rr \in TranExclusive(seq[i].mm)  BY <2>rr DEF Qd
  <2>rrTran. seq[i].rr \in Tran(seq[i].mm)  BY <2>rrTE DEF TranExclusive
  <2>rrTC. seq[i].rr \in TranClosure(mset)  BY <2>rrTran, <2>mmMsg
  <2>rrMsg. seq[i].rr \in Messages /\ Tran(seq[i].rr) \subseteq TranClosure(mset)
    BY <2>rrTC, <1>mi, TranClosureClosed
  <2>ss. seq[i].ss \in Tran(seq[i].rr)  BY <2>cc DEF TraceCondCore
  <2>ssTC. seq[i].ss \in TranClosure(mset)  BY <2>ss, <2>rrMsg
  <2> QED BY <2>mmTC, <2>rrTC, <2>ssTC
<1>eltMsg. \A i \in 1..K : seq[i].mm \in Messages /\ seq[i].rr \in Messages /\ seq[i].ss \in Messages
  <2> SUFFICES ASSUME NEW i \in 1..K
               PROVE seq[i].mm \in Messages /\ seq[i].rr \in Messages /\ seq[i].ss \in Messages
    OBVIOUS
  <2> QED BY <1>elt, <1>mi, TranClosureClosed
<1>onestep. \A i \in 1..(K-1) : seq[i+1].rr \in Tran(seq[i].rr)
  <2> SUFFICES ASSUME NEW i \in 1..(K-1) PROVE seq[i+1].rr \in Tran(seq[i].rr)  OBVIOUS
  <2>i1dom. i+1 \in 1..K  OBVIOUS
  <2>cc. TraceCondCore(alpha, lobal, TranClosure(mset), himsg, seq, i+1)  BY <2>i1dom
  <2>gt1. i+1 > 1  OBVIOUS
  <2>mm. seq[i+1].mm \in Tran(seq[i].rr)  BY <2>cc, <2>gt1 DEF TraceCondCore
  <2>rr. seq[i+1].rr \in Qd(seq[i+1].gamma, seq[i+1].mm, 1)  BY <2>cc DEF TraceCondCore
  <2>rrTE. seq[i+1].rr \in TranExclusive(seq[i+1].mm)  BY <2>rr DEF Qd
  <2>rrTran. seq[i+1].rr \in Tran(seq[i+1].mm)  BY <2>rrTE DEF TranExclusive
  <2>iInK. i \in 1..K  OBVIOUS
  <2>iMsg. seq[i].rr \in Messages  BY <2>iInK, <1>elt, <1>mi, TranClosureClosed
  <2>trans. Tran(seq[i+1].mm) \subseteq Tran(seq[i].rr)  BY <2>mm, <2>iMsg, <1>mi DEF TranTrans
  <2> QED BY <2>rrTran, <2>trans
<1>chain. \A i \in 1..K : \A j \in 1..K : i <= j => seq[j].rr \in Tran(seq[i].rr)
  <2> DEFINE Q(d) == \A i \in 1..K : (i+d \in 1..K) => seq[i+d].rr \in Tran(seq[i].rr)
  <2> SUFFICES \A d \in Nat : Q(d)
    <3> SUFFICES ASSUME NEW i \in 1..K, NEW j \in 1..K, i <= j
                 PROVE seq[j].rr \in Tran(seq[i].rr)
      OBVIOUS
    <3>1. j - i \in Nat  OBVIOUS
    <3>2. Q(j-i)  BY <3>1
    <3>3. i + (j-i) \in 1..K  OBVIOUS
    <3> QED BY <3>2, <3>3
  <2> HIDE DEF Q
  <2>ind. \A d \in Nat : (\A k \in 0..(d-1) : Q(k)) => Q(d)
    <3> USE DEF Q
    <3> SUFFICES ASSUME NEW d \in Nat, \A k \in 0..(d-1) : Q(k),
                        NEW i \in 1..K, i+d \in 1..K
                 PROVE seq[i+d].rr \in Tran(seq[i].rr)
      OBVIOUS
    <3>a. CASE d = 0
      <4>1. i + d = i  BY <3>a
      <4> QED BY <4>1 DEF Tran
    <3>b. CASE d >= 1
      <4>i1dom. i + 1 \in 1..K  BY <3>b
      <4>dm1nat. d - 1 \in Nat /\ d - 1 \in 0..(d-1)  BY <3>b
      <4>ih. Q(d-1)  BY <4>dm1nat
      <4>sum. (i+1) + (d-1) \in 1..K
        <5>1. (i+1) + (d-1) = i + d  BY <3>b
        <5> QED BY <5>1
      <4>rec. seq[(i+1)+(d-1)].rr \in Tran(seq[i+1].rr)  BY <4>ih, <4>i1dom, <4>sum
      <4>eq. (i+1) + (d-1) = i + d  BY <3>b
      <4>onestepAt. seq[i+1].rr \in Tran(seq[i].rr)
        <5>1. i \in 1..(K-1)  BY <3>b, <4>i1dom
        <5> QED BY <5>1, <1>onestep
      <4>rMsg. seq[i+1].rr \in Messages  BY <4>i1dom, <1>eltMsg
      <4>iMsg. seq[i].rr \in Messages  BY <1>eltMsg
      <4>trans. Tran(seq[i+1].rr) \subseteq Tran(seq[i].rr)
        BY <4>onestepAt, <4>iMsg, <1>mi DEF TranTrans
      <4> QED BY <4>rec, <4>eq, <4>trans
    <3> QED BY <3>a, <3>b
  <2> QED BY <2>ind, GeneralNatInduction, IsaM("blast")
<1>bpart. \A i, j \in 1..K : i < j => seq[j].rr \in Tran(seq[i].rr)
  <2> SUFFICES ASSUME NEW i \in 1..K, NEW j \in 1..K, i < j
               PROVE seq[j].rr \in Tran(seq[i].rr)  OBVIOUS
  <2>1. i <= j  OBVIOUS
  <2> QED BY <2>1, <1>chain
<1>submono. \A i \in 1..K : \A j \in 1..K : i <= j => Con(alpha, seq[i].rr) \subseteq Con(alpha, seq[j].rr)
  <2> SUFFICES ASSUME NEW i \in 1..K, NEW j \in 1..K, i <= j
               PROVE Con(alpha, seq[i].rr) \subseteq Con(alpha, seq[j].rr)
    OBVIOUS
  <2>1. CASE i = j  BY <2>1
  <2>2. CASE i < j
    <3>1. seq[j].rr \in Tran(seq[i].rr)  BY <1>chain, <2>2
    <3>2. seq[i].rr \in Messages  BY <1>elt, <1>mi, TranClosureClosed
    <3> QED BY <3>1, <3>2, <1>mi, ConMonotoneTran
  <2> QED BY <2>1, <2>2
<1>cpart. \A i, j \in 1..K : (i < j /\ j < K) =>
             /\ Con(alpha, seq[i].rr) \subseteq Con(alpha, seq[j].rr)
             /\ Con(alpha, seq[i].rr) # Con(alpha, seq[j].rr)
  <2> SUFFICES ASSUME NEW i \in 1..K, NEW j \in 1..K, i < j, j < K
               PROVE /\ Con(alpha, seq[i].rr) \subseteq Con(alpha, seq[j].rr)
                     /\ Con(alpha, seq[i].rr) # Con(alpha, seq[j].rr)
    OBVIOUS
  <2>sub. Con(alpha, seq[i].rr) \subseteq Con(alpha, seq[j].rr)  BY <1>submono
  <2>j1dom. j + 1 \in 1..K  OBVIOUS
  <2>jm1dom. j - 1 \in 1..K  OBVIOUS
  <2>cc. TraceCondCore(alpha, lobal, TranClosure(mset), himsg, seq, j+1)  BY <2>j1dom
  <2>g5. seq[j+1].gamma \in Con(alpha, seq[j].rr)
    <3>1. j + 1 > 1  OBVIOUS
    <3> QED BY <2>cc, <3>1 DEF TraceCondCore
  <2>g6. seq[j+1].gamma \notin Con(alpha, seq[j-1].rr)
    <3>1. j + 1 > 2  OBVIOUS
    <3> QED BY <2>cc, <3>1 DEF TraceCondCore
  <2>subij. Con(alpha, seq[i].rr) \subseteq Con(alpha, seq[j-1].rr)
    <3>1. i <= j - 1  OBVIOUS
    <3> QED BY <1>submono, <3>1, <2>jm1dom
  <2>notmem. seq[j+1].gamma \notin Con(alpha, seq[i].rr)
    <3> SUFFICES ASSUME seq[j+1].gamma \in Con(alpha, seq[i].rr) PROVE FALSE  OBVIOUS
    <3>1. seq[j+1].gamma \in Con(alpha, seq[j-1].rr)  BY <2>subij
    <3> QED BY <3>1, <2>g6
  <2>diff. Con(alpha, seq[i].rr) # Con(alpha, seq[j].rr)  BY <2>g5, <2>notmem
  <2> QED BY <2>sub, <2>diff
<1> QED BY <1>elt, <1>bpart, <1>cpart

\* A full-length minimal trace is impossible: prepending Acceptors (whose
\* ConFromCaught is empty) and CaughtS(closure) (whose ConFromCaught
\* contains beta but, by minimality of B(seq[1].mm), NOT seq[2].gamma) to
\* the shrinking caught sets Caught(seq[x].rr) yields a ValidSeqs(alpha)
\* chain of length MaxDepth(alpha) + 2, contradicting ValidSeqsLenMaxDepth.
\* Consumes only the core+minimality conditions, so it serves both the slow
\* and the fast induction.
LEMMA TraceContradiction ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions,
         ValueInterfaceAssumptions,
         NEW mset \in SUBSET Messages,
         NEW alpha \in Learners, NEW beta \in Learners,
         NEW lobal \in Ballots,
         NEW himsg \in TranClosure(mset),
         beta \in ConFromCaught(alpha, CaughtS(TranClosure(mset))),
         NEW seq \in [1..MaxDepth(alpha)+1 -> TraceElem],
         \A x \in 1..MaxDepth(alpha)+1 :
           TraceCondCoreMin(alpha, lobal, TranClosure(mset), himsg, seq, x)
  PROVE FALSE
<1> DEFINE K == MaxDepth(alpha) + 1
<1> DEFINE CL == TranClosure(mset)
<1>mi. TypeOKMessageInterface /\ TranFinite /\ TranTrans /\ TranAcyclic /\ AlwaysAProposal
  BY DEF MessageInterfaceAssumptions
<1>lg. FiniteAcceptors /\ FiniteLearners /\ LearnersNonEmpty /\ QuorumsNonEmpty
       /\ LearnersMightAgree /\ CondensedLearnerGraphAssumption /\ ValidLearnerGraphAssumption
  BY DEF LearnerGraphAssumptions
<1>Kge2. K >= 2 /\ K \in Nat /\ MaxDepth(alpha) \in Nat
  <2>1. MaxDepth(alpha) \in 1..Cardinality(Acceptors)  BY <1>lg, MaxDepthFiniteAcceptors
  <2> QED BY <2>1
<1> USE <1>Kge2
<1>core. \A x \in 1..K : TraceCondCore(alpha, lobal, CL, himsg, seq, x)
  <2> SUFFICES ASSUME NEW x \in 1..K PROVE TraceCondCore(alpha, lobal, CL, himsg, seq, x)  OBVIOUS
  <2> QED BY DEF TraceCondCoreMin
<1>tcp. /\ \A i \in 1..K : /\ seq[i].mm \in CL /\ seq[i].rr \in CL /\ seq[i].ss \in CL
        /\ \A i, j \in 1..K : i < j => seq[j].rr \in Tran(seq[i].rr)
        /\ \A i, j \in 1..K : (i < j /\ j < K) =>
             /\ Con(alpha, seq[i].rr) \subseteq Con(alpha, seq[j].rr)
             /\ Con(alpha, seq[i].rr) # Con(alpha, seq[j].rr)
  BY <1>core, <1>Kge2, TraceCoreProperties
<1>tcpA. \A i \in 1..K : seq[i].mm \in CL /\ seq[i].rr \in CL /\ seq[i].ss \in CL  BY <1>tcp
<1>tcpB. \A i, j \in 1..K : i < j => seq[j].rr \in Tran(seq[i].rr)  BY <1>tcp
<1>tcpC. \A i, j \in 1..K : (i < j /\ j < K) =>
             Con(alpha, seq[i].rr) \subseteq Con(alpha, seq[j].rr) /\ Con(alpha, seq[i].rr) # Con(alpha, seq[j].rr)
  BY <1>tcp
\* seq[2].gamma is NOT connected given only CaughtS(closure): otherwise the
\* record z below (= seq[2], relabelled to index 1) would be a valid <1>
\* candidate with a strictly lower Cardinality(Tran(.)) than seq[1].mm (via
\* <1>2's own item 3), contradicting seq[1]'s minimality (TraceCondCoreMin).
<1>notin2. seq[2].gamma \notin ConFromCaught(alpha, CaughtS(CL))
  <2> SUFFICES ASSUME seq[2].gamma \in ConFromCaught(alpha, CaughtS(CL)) PROVE FALSE  OBVIOUS
  <2>1dom. 1 \in 1..K  BY <1>Kge2
  <2>2dom. 2 \in 1..K  BY <1>Kge2
  <2>min1. TraceCondCoreMin(alpha, lobal, CL, himsg, seq, 1)  BY <2>1dom
  <2>c2. TraceCondCore(alpha, lobal, CL, himsg, seq, 2)  BY <2>2dom DEF TraceCondCoreMin
  <2> DEFINE z == [mm |-> seq[2].mm, rr |-> seq[2].rr, ss |-> seq[2].ss, gamma |-> seq[2].gamma]
  <2>zType. z \in TraceElem
    <3>1. seq[2].mm \in Messages /\ seq[2].rr \in Messages /\ seq[2].ss \in Messages /\ seq[2].gamma \in Learners
      <4>inCL. seq[2].mm \in CL /\ seq[2].rr \in CL /\ seq[2].ss \in CL  BY <1>tcpA, <2>2dom
      <4>clsub. CL \subseteq Messages
        <5> SUFFICES ASSUME NEW y \in CL PROVE y \in Messages  OBVIOUS
        <5> QED BY <1>mi, TranClosureClosed
      <4>gam. seq[2].gamma \in Learners  BY <2>c2 DEF TraceCondCore, Lrns
      <4> QED BY <4>inCL, <4>clsub, <4>gam
    <3> QED BY <3>1 DEF TraceElem
  <2>zmm. z.mm = seq[2].mm  OBVIOUS
  <2>i1. TraceCondCore(alpha, lobal, CL, himsg, [seq EXCEPT ![1] = z], 1)
    <3> DEFINE seq2 == [seq EXCEPT ![1] = z]
    <3>s1. seq2[1] = z  BY <1>Kge2
    <3>c1. /\ z.mm \in Tran(himsg)
           /\ lobal < B(z.mm)
           /\ z.gamma \in Lrns(z.mm)
           /\ z.rr \in Qd(z.gamma, z.mm, 1)
           /\ z.ss \in Tran(z.rr)
           /\ Sig(z.rr) = Sig(z.ss)
           /\ B(z.ss) = lobal
           /\ V(z.mm) = V(himsg)
      BY <2>c2 DEF TraceCondCore
    <3>c1a. z.gamma \in ConFromCaught(alpha, CaughtS(CL))  OBVIOUS
    <3> QED BY <3>s1, <3>c1, <3>c1a DEF TraceCondCore
  <2>minapp. Cardinality(Tran(seq[1].mm)) <= Cardinality(Tran(z.mm))
    BY <2>min1, <2>zType, <2>i1 DEF TraceCondCoreMin
  <2>lt. Cardinality(Tran(seq[2].mm)) < Cardinality(Tran(seq[1].mm))
    <3>1. 2 > 1 /\ 2 - 1 = 1  OBVIOUS
    <3> QED BY <2>c2, <3>1 DEF TraceCondCore
  <2>ty. Cardinality(Tran(seq[1].mm)) \in Nat /\ Cardinality(Tran(seq[2].mm)) \in Nat
    <3>1. seq[1].mm \in CL /\ seq[2].mm \in CL  BY <1>tcpA, <2>1dom, <2>2dom
    <3>2. seq[1].mm \in Messages /\ seq[2].mm \in Messages  BY <3>1, <1>mi, TranClosureClosed
    <3> QED BY <3>2, <1>mi, TranCardNat
  <2> QED BY <2>minapp, <2>zmm, <2>lt, <2>ty
\* the chain: Acceptors, CaughtS(closure), Caught(seq[1].rr), .., Caught(seq[K-1].rr)
<1> DEFINE l == [i \in 1..(K+1) |->
      IF i = 1 THEN Acceptors
      ELSE IF i = 2 THEN CaughtS(CL)
      ELSE Caught(seq[i-2].rr)]
<1>lrange. \A i \in 1..(K+1) : l[i] \subseteq Acceptors
  <2> SUFFICES ASSUME NEW i \in 1..(K+1) PROVE l[i] \subseteq Acceptors  OBVIOUS
  <2>1. CASE i = 1  BY <2>1
  <2>2. CASE i = 2  BY <2>2 DEF CaughtS
  <2>3. CASE i \notin {1,2}
    <3>1. l[i] = Caught(seq[i-2].rr)  BY <2>3
    <3> QED BY <3>1 DEF Caught, CaughtS
  <2> QED BY <2>1, <2>2, <2>3
<1>lfun. l \in [1..(K+1) -> SUBSET Acceptors]  BY <1>lrange
<1>lseq. l \in Seq(SUBSET Acceptors)
  <2>1. K + 1 \in Nat  BY <1>Kge2
  <2> QED BY <1>lfun, <2>1, SeqDef
<1>llen. Len(l) = K + 1
  <2>props. Len(l) \in Nat /\ DOMAIN l = 1..Len(l)  BY <1>lseq, LenProperties
  <2>dom. DOMAIN l = 1..(K+1)  OBVIOUS
  <2>eq. 1..Len(l) = 1..(K+1)  BY <2>props, <2>dom
  <2>in1. K + 1 \in 1..(K+1)  BY <1>Kge2
  <2>le1. K + 1 <= Len(l)
    <3>1. K + 1 \in 1..Len(l)  BY <2>eq, <2>in1
    <3> QED BY <3>1, <2>props
  <2>le2. Len(l) <= K + 1
    <3>1. Len(l) \in 1..Len(l)  BY <2>props, <2>le1, <1>Kge2
    <3>2. Len(l) \in 1..(K+1)  BY <3>1, <2>eq
    <3> QED BY <3>2
  <2> QED BY <2>le1, <2>le2, <2>props, <1>Kge2
<1>trans. \A i \in 1..K : l[i+1] \subseteq l[i] /\ ConFromCaught(alpha, l[i]) # ConFromCaught(alpha, l[i+1])
  <2> SUFFICES ASSUME NEW i \in 1..K
               PROVE l[i+1] \subseteq l[i] /\ ConFromCaught(alpha, l[i]) # ConFromCaught(alpha, l[i+1])
    OBVIOUS
  <2>a. CASE i = 1
    <3>l1. l[1] = Acceptors  BY <2>a
    <3>l2. l[2] = CaughtS(CL)  BY <2>a
    <3>sub. l[2] \subseteq l[1]  BY <3>l1, <3>l2 DEF CaughtS
    <3>con1. ConFromCaught(alpha, Acceptors) = {}  BY <1>lg, ConFromCaughtAllCaught
    <3>betaIn. beta \in ConFromCaught(alpha, CaughtS(CL))  OBVIOUS
    <3>ne2. ConFromCaught(alpha, CaughtS(CL)) # {}  BY <3>betaIn
    <3>diff. ConFromCaught(alpha, l[1]) # ConFromCaught(alpha, l[2])  BY <3>l1, <3>l2, <3>con1, <3>ne2
    <3> QED BY <3>sub, <3>diff, <2>a
  <2>b. CASE i = 2
    <3>l2. l[2] = CaughtS(CL)  BY <2>b
    <3>l3. l[3] = Caught(seq[1].rr)  BY <2>b
    <3>rTC. seq[1].rr \in CL
      <4>1dom. 1 \in 1..K  BY <1>Kge2
      <4> QED BY <4>1dom, <1>tcpA
    <3>sub. l[3] \subseteq l[2]  BY <3>l3, <3>l2, <3>rTC, <1>mi, CaughtSubClosure
    <3>betaIn. beta \in ConFromCaught(alpha, l[2])  BY <3>l2
    <3>notin. seq[2].gamma \notin ConFromCaught(alpha, l[2])  BY <3>l2, <1>notin2
    <3>2dom. 2 \in 1..K  BY <1>Kge2
    <3>c2. TraceCondCore(alpha, lobal, CL, himsg, seq, 2)  BY <3>2dom DEF TraceCondCoreMin
    <3>g5in. seq[2].gamma \in Con(alpha, seq[1].rr)
      <4>1. 2 > 1  OBVIOUS
      <4> QED BY <3>c2, <4>1 DEF TraceCondCore
    <3>g5in2. seq[2].gamma \in ConFromCaught(alpha, l[3])  BY <3>g5in, <3>l3 DEF Con
    <3>diff. ConFromCaught(alpha, l[2]) # ConFromCaught(alpha, l[3])  BY <3>notin, <3>g5in2
    <3> QED BY <3>sub, <3>diff, <2>b
  <2>c. CASE i \notin {1,2}
    <3>x. i - 2 \in 1..(K-1)  BY <2>c
    <3>li. l[i] = Caught(seq[i-2].rr)  BY <2>c
    <3>eqidx. (i+1) - 2 = (i - 2) + 1  OBVIOUS
    <3>li1. l[i+1] = Caught(seq[(i-2)+1].rr)  BY <2>c, <3>eqidx
    <3>domA. i - 2 \in 1..K  BY <3>x
    <3>domB. (i-2)+1 \in 1..K  BY <3>x
    <3>lt. (i-2) < (i-2)+1  OBVIOUS
    <3>rrTran. seq[(i-2)+1].rr \in Tran(seq[i-2].rr)  BY <3>domA, <3>domB, <3>lt, <1>tcpB
    <3>sub. l[i+1] \subseteq l[i]
      <4>m. seq[i-2].rr \in Messages
        <5>1. seq[i-2].rr \in CL  BY <1>tcpA, <3>domA
        <5> QED BY <5>1, <1>mi, TranClosureClosed
      <4>1. Caught(seq[(i-2)+1].rr) \subseteq Caught(seq[i-2].rr)
        BY <3>rrTran, <4>m, <1>mi, CaughtMonotoneTran
      <4> QED BY <4>1, <3>li, <3>li1
    <3>jltK. (i-2)+1 < K  BY <3>x
    <3>diffCon. Con(alpha, seq[i-2].rr) # Con(alpha, seq[(i-2)+1].rr)
      BY <3>domA, <3>domB, <3>lt, <3>jltK, <1>tcpC
    <3>diff. ConFromCaught(alpha, l[i]) # ConFromCaught(alpha, l[i+1])
      <4>1. ConFromCaught(alpha, Caught(seq[i-2].rr)) # ConFromCaught(alpha, Caught(seq[(i-2)+1].rr))
        BY <3>diffCon DEF Con
      <4> QED BY <4>1, <3>li, <3>li1
    <3> QED BY <3>sub, <3>diff
  <2> QED BY <2>a, <2>b, <2>c
<1>valid. l \in ValidSeqs(alpha)
  <2>idx. 1..(Len(l)-1) = 1..K  BY <1>llen
  <2> QED BY <1>lseq, <1>trans, <2>idx DEF ValidSeqs
<1>bound. Len(l) - 1 <= MaxDepth(alpha)  BY <1>valid, <1>lg, ValidSeqsLenMaxDepth
<1> QED BY <1>bound, <1>llen

\* Given any valid (g,m) pairing -- m in the closure, g connected to alpha,
\* g a learner of m, and m's ballot above lobal -- produces a matching
\* (rr,ss) pair: rr is g's own depth-1 witness at m, ss agrees with rr's
\* signer and sits at ballot lobal with alpha's own full MaxDepth witness
\* (drawn from the slow decision's quorum W).  Construction: g in Lrns(m)
\* gives a g-quorum via Qd(g,m,1); DecisionSlow gives an alpha-quorum W;
\* the two intersect (SafeQuorumsIntersectUncaught, through g's safety set
\* with alpha) in an uncaught acceptor signing both an r0 in Qd(g,m,1) and
\* an s0 in W -- same signer, uncaught, so Tran-comparable
\* (UncaughtSameSigComparable); the direction s0 in Tran(r0) is forced
\* because B(r0)=B(m)>lobal=B(s0) rules out the reverse via BMonotone.
LEMMA SlowSupportWitness ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions,
         NEW mset \in SUBSET Messages,
         NEW alpha \in Learners, NEW lobal \in Ballots,
         DecisionSlow(mset, alpha, lobal),
         NEW g \in Learners, g \in ConFromCaught(alpha, CaughtS(TranClosure(mset))),
         NEW m \in TranClosure(mset), g \in Lrns(m), lobal < B(m)
  PROVE \E rr \in Qd(g, m, 1) : \E ss \in Tran(rr) :
          /\ Sig(rr) = Sig(ss)
          /\ B(ss) = lobal
          /\ HasDepth(alpha, ss, MaxDepth(alpha))
<1> DEFINE W == {x \in TranClosure(mset) : B(x) = lobal /\ HasDepth(alpha, x, MaxDepth(alpha))}
<1>mi. TypeOKMessageInterface /\ TranFinite /\ TranTrans /\ TranAcyclic /\ AlwaysAProposal
  BY DEF MessageInterfaceAssumptions
<1>lgv. ValidLearnerGraphAssumption  BY DEF LearnerGraphAssumptions
<1>mM. m \in Messages  BY <1>mi, TranClosureClosed
<1>sigW. SigS(W) \in Quorums(alpha)  BY DEF DecisionSlow
<1>lrn. HasDepth(g, m, 1)  BY DEF Lrns
<1>hd1. Sig(m) \in Acceptors /\ SigS(Qd(g, m, 1)) \in Quorums(g)
  <2>1. 1 \in Nat /\ 1 # 0  OBVIOUS
  <2>2. HasDepth(g, m, 1) =
          (/\ Sig(m) \in Acceptors
           /\ IF 1 = 0 THEN (IsOneB(m) /\ Fresh(g, m))
                       ELSE SigS(Qd(g, m, 1)) \in Quorums(g))
    BY <1>mi, <1>mM, <2>1, HasDepthDef
  <2> QED BY <1>lrn, <2>1, <2>2
<1>q2. SigS(Qd(g, m, 1)) \in Quorums(g)  BY <1>hd1
<1>con. PICK s \in SafetySets({alpha, g}) : s \cap CaughtS(TranClosure(mset)) = {}  BY DEF ConFromCaught
<1>inter. \E a \in Acceptors : a \in SigS(W) /\ a \in SigS(Qd(g,m,1)) /\ a \notin CaughtS(TranClosure(mset))
  BY <1>con, <1>sigW, <1>q2, <1>lgv, SafeQuorumsIntersectUncaught
<1> PICK a \in Acceptors : a \in SigS(W) /\ a \in SigS(Qd(g,m,1)) /\ a \notin CaughtS(TranClosure(mset))
  BY <1>inter
<1>s0. PICK s0 \in W : a = Sig(s0)  BY DEF SigS
<1>r0. PICK r0 \in Qd(g,m,1) : a = Sig(r0)  BY DEF SigS
<1>s0M. s0 \in TranClosure(mset) /\ B(s0) = lobal /\ HasDepth(alpha, s0, MaxDepth(alpha))  BY <1>s0
<1>r0Q. r0 \in TranExclusive(m) /\ B(m) = B(r0)  BY <1>r0 DEF Qd
<1>r0B. B(r0) = B(m)  BY <1>r0Q
<1>s0inCL. s0 \in TranClosure(mset)  BY <1>s0M
<1>r0inCL. r0 \in TranClosure(mset)
  <2>1. r0 \in Tran(m)  BY <1>r0Q DEF TranExclusive
  <2>2. m \in Messages /\ Tran(m) \subseteq TranClosure(mset)  BY <1>mi, TranClosureClosed
  <2> QED BY <2>1, <2>2
<1>cmp. s0 \in Tran(r0) \/ r0 \in Tran(s0)
  BY <1>s0inCL, <1>r0inCL, UncaughtSameSigComparable, <1>s0, <1>r0
<1>notRev. r0 \notin Tran(s0)
  <2> SUFFICES ASSUME r0 \in Tran(s0) PROVE FALSE  OBVIOUS
  <2>1. s0 \in Messages  BY <1>s0inCL, <1>mi, TranClosureClosed
  <2>2. B(r0) <= B(s0)  BY <2>1, <1>mi, BMonotone
  <2>3. B(r0) = B(m)  BY <1>r0B
  <2>4. B(s0) = lobal  BY <1>s0M
  <2>5. B(m) \in Nat /\ lobal \in Nat
    <3>1. B(m) \in Ballots  BY <1>mi, <1>mM, BBallot
    <3> QED BY <3>1 DEF Ballots
  <2> QED BY <2>2, <2>3, <2>4, <2>5
<1>ss0Tran. s0 \in Tran(r0)  BY <1>cmp, <1>notRev
<1>sigeq. Sig(r0) = Sig(s0)  BY <1>r0, <1>s0
<1> QED BY <1>r0, <1>ss0Tran, <1>sigeq, <1>s0M

\* The step-level analogue of SlowSupportWitness, at an arbitrary anchor
\* rlev in the chain: given a learner g connected to alpha AS OF rlev, a
\* g-attested message mm inside Tran(rlev), and an alpha-side support
\* message slev in Tran(rlev) at ballot lobal with dep depth levels left,
\* produce a same-signer pair (rr, ss): rr a depth-1 witness of mm for g,
\* ss one level down slev's own quorum tree.  The two quorums intersect
\* through g's uncaught-as-of-rlev safety set; both members live in
\* Tran(rlev), so the uncaught common signer makes them Tran-comparable,
\* and B(ss) = lobal < B(mm) = B(rr) forces the direction ss \in Tran(rr).
LEMMA TraceStepWitness ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions,
         NEW alpha \in Learners, NEW g \in Learners,
         NEW lobal \in Ballots,
         NEW rlev \in Messages, NEW slev \in Messages, NEW mm \in Messages,
         NEW dep \in Nat, dep >= 1,
         g \in Con(alpha, rlev),
         g \in Lrns(mm),
         mm \in Tran(rlev),
         slev \in Tran(rlev),
         B(slev) = lobal,
         lobal < B(mm),
         HasDepth(alpha, slev, dep)
  PROVE \E rr \in Qd(g, mm, 1) : \E ss \in Qd(alpha, slev, dep) :
          Sig(rr) = Sig(ss) /\ ss \in Tran(rr)
<1>mi. TypeOKMessageInterface /\ TranFinite /\ TranTrans /\ TranAcyclic /\ AlwaysAProposal
  BY DEF MessageInterfaceAssumptions
<1>lg. ValidLearnerGraphAssumption  BY DEF LearnerGraphAssumptions
<1>q1. SigS(Qd(g, mm, 1)) \in Quorums(g)
  <2>1. HasDepth(g, mm, 1)  BY DEF Lrns
  <2>2. 1 \in Nat /\ 1 # 0  OBVIOUS
  <2>3. HasDepth(g, mm, 1) =
          (/\ Sig(mm) \in Acceptors
           /\ IF 1 = 0 THEN (IsOneB(mm) /\ Fresh(g, mm))
                       ELSE SigS(Qd(g, mm, 1)) \in Quorums(g))
    BY <1>mi, <2>2, HasDepthDef
  <2> QED BY <2>1, <2>2, <2>3
<1>q2. SigS(Qd(alpha, slev, dep)) \in Quorums(alpha)
  <2>1. dep # 0  OBVIOUS
  <2>2. HasDepth(alpha, slev, dep) =
          (/\ Sig(slev) \in Acceptors
           /\ IF dep = 0 THEN (IsOneB(slev) /\ Fresh(alpha, slev))
                         ELSE SigS(Qd(alpha, slev, dep)) \in Quorums(alpha))
    BY <1>mi, HasDepthDef
  <2> QED BY <2>1, <2>2
<1>s. PICK s \in SafetySets({alpha, g}) : s \cap Caught(rlev) = {}
  BY DEF Con, ConFromCaught
<1>a. PICK a \in Acceptors :
        a \in SigS(Qd(alpha, slev, dep)) /\ a \in SigS(Qd(g, mm, 1)) /\ a \notin Caught(rlev)
  BY <1>lg, <1>s, <1>q1, <1>q2, SafeQuorumsIntersectUncaught
<1>ss. PICK ss \in Qd(alpha, slev, dep) : a = Sig(ss)  BY <1>a DEF SigS
<1>rr. PICK rr \in Qd(g, mm, 1) : a = Sig(rr)  BY <1>a DEF SigS
<1>ssP. ss \in TranExclusive(slev) /\ B(ss) = B(slev)
  <2>1. ss \in TranExclusive(slev) /\ B(slev) = B(ss)  BY <1>ss, <1>mi DEF Qd
  <2> QED BY <2>1
<1>rrP. rr \in TranExclusive(mm) /\ B(rr) = B(mm)
  <2>1. rr \in TranExclusive(mm) /\ B(mm) = B(rr)  BY <1>rr, <1>mi DEF Qd
  <2> QED BY <2>1
<1>ssT. ss \in Tran(rlev)
  <2>1. ss \in Tran(slev)  BY <1>ssP DEF TranExclusive
  <2>2. Tran(slev) \subseteq Tran(rlev)  BY <1>mi DEF TranTrans
  <2> QED BY <2>1, <2>2
<1>rrT. rr \in Tran(rlev)
  <2>1. rr \in Tran(mm)  BY <1>rrP DEF TranExclusive
  <2>2. Tran(mm) \subseteq Tran(rlev)  BY <1>mi DEF TranTrans
  <2> QED BY <2>1, <2>2
<1>cmp. ss \in Tran(rr) \/ rr \in Tran(ss)
  <2>1. a \notin CaughtS(Tran(rlev))  BY <1>a DEF Caught
  <2> QED BY <2>1, <1>ssT, <1>rrT, <1>ss, <1>rr, UncaughtSameSigComparable
<1>ssM. ss \in Messages
  <2>1. Tran(rlev) \subseteq Messages  BY <1>mi, TranSubMessages
  <2> QED BY <1>ssT, <2>1
<1>bmm. B(mm) \in Ballots  BY <1>mi, BBallot
<1>notrev. rr \notin Tran(ss)
  <2> SUFFICES ASSUME rr \in Tran(ss) PROVE FALSE  OBVIOUS
  <2>1. B(rr) <= B(ss)  BY <1>mi, <1>ssM, BMonotone
  <2>2. B(rr) = B(mm)  BY <1>rrP
  <2>3. B(ss) = lobal  BY <1>ssP
  <2>4. B(mm) \in Nat /\ lobal \in Nat  BY <1>bmm DEF Ballots
  <2> QED BY <2>1, <2>2, <2>3, <2>4
<1>dir. ss \in Tran(rr)  BY <1>cmp, <1>notrev
<1>sig. Sig(rr) = Sig(ss)  BY <1>rr, <1>ss
<1> QED BY <1>rr, <1>ss, <1>sig, <1>dir

\* Slow-decision trace existence (paper Lemma 25's induction; hpaxos-tla
\* HeterogeneousTraceExistence).  Induction on i: the base element pairs
\* himsg with a decision-quorum member (SlowSupportWitness); the step
\* extracts the next mm via FreshTopConnected applied to rr_n at w = ss_n
\* (whose positive remaining depth registers alpha in Lrns(ss_n), refuting
\* Fresh's second disjunct), realizes minimality by
\* ExistsMinTranCardElement, and re-witnesses rr/ss at the minimal mm by
\* TraceStepWitness, spending one depth level of budget.  Item 6 for the
\* new element is the k* argument (hpaxos-tla's <4>6): take the LEAST index
\* kst at which the new learner is connected; substituting the freshly
\* re-witnessed element at kst+1 satisfies the core there -- item 5 is the
\* definition of kst, item 6 its minimality -- so the minimality of
\* seq[kst+1] bounds Cardinality(Tran(seq[kst+1].mm)) by
\* Cardinality(Tran(p)), contradicting the chain's strict descent.
LEMMA TraceExistenceSlow ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions,
         ValueInterfaceAssumptions,
         NEW mset \in SUBSET Messages,
         NEW alpha \in Learners, NEW beta \in Learners,
         NEW lobal \in Ballots, NEW hibal \in Ballots,
         lobal < hibal,
         BalToVal(lobal) # BalToVal(hibal),
         DecisionSlow(mset, alpha, lobal),
         beta \in ConFromCaught(alpha, CaughtS(TranClosure(mset))),
         NEW himsg \in TranClosure(mset),
         B(himsg) = hibal,
         beta \in Lrns(himsg)
  PROVE \A i \in 0..MaxDepth(alpha) :
          \E seq \in [1..i+1 -> TraceElem] :
            \A x \in 1..i+1 :
              /\ TraceCondCoreMin(alpha, lobal, TranClosure(mset), himsg, seq, x)
              /\ TraceBudgetSlow(alpha, seq, x)
<1> DEFINE CL == TranClosure(mset)
<1> DEFINE MD == MaxDepth(alpha)
<1>mi. TypeOKMessageInterface /\ TranFinite /\ TranTrans /\ TranAcyclic /\ AlwaysAProposal
  BY DEF MessageInterfaceAssumptions
<1>lg. FiniteAcceptors /\ FiniteLearners /\ LearnersNonEmpty /\ QuorumsNonEmpty
       /\ LearnersMightAgree /\ CondensedLearnerGraphAssumption /\ ValidLearnerGraphAssumption
  BY DEF LearnerGraphAssumptions
<1>md. MD \in Nat /\ MD >= 1
  <2>1. MD \in 1..Cardinality(Acceptors)  BY <1>lg, MaxDepthFiniteAcceptors
  <2> QED BY <2>1
<1>clM. CL \subseteq Messages
  <2> SUFFICES ASSUME NEW y \in CL PROVE y \in Messages  OBVIOUS
  <2> QED BY <1>mi, TranClosureClosed
<1>hiM. himsg \in Messages  BY <1>clM
<1>hiTr. Tran(himsg) \subseteq CL  BY <1>mi, TranClosureClosed
<1>vhi. V(himsg) = BalToVal(hibal)  BY DEF V
<1> DEFINE Q(n) == n \in 0..MD =>
      \E sq0 \in [1..n+1 -> TraceElem] :
        \A x \in 1..n+1 :
          /\ TraceCondCoreMin(alpha, lobal, CL, himsg, sq0, x)
          /\ TraceBudgetSlow(alpha, sq0, x)
<1> SUFFICES \A n \in Nat : Q(n)
  <2>1. \A i \in 0..MD : i \in Nat  OBVIOUS
  <2> QED BY <2>1 DEF Q
<1> HIDE DEF Q
<1>ind. \A n \in Nat : (\A kk \in 0..(n-1) : Q(kk)) => Q(n)
  \* Q is kept FOLDED throughout the step (no blanket USE DEF Q): the
  \* ambient course-of-values hypothesis would otherwise expand inside
  \* every one of the ~950 obligations below and blow their contexts up.
  \* Only the two steps that genuinely unfold Q cite its definition.
  <2> SUFFICES ASSUME NEW n \in Nat, \A kk \in 0..(n-1) : Q(kk), n \in 0..MD
               PROVE \E sq0 \in [1..n+1 -> TraceElem] :
                       \A x \in 1..n+1 :
                         /\ TraceCondCoreMin(alpha, lobal, CL, himsg, sq0, x)
                         /\ TraceBudgetSlow(alpha, sq0, x)
    BY DEF Q
  <2>base. CASE n = 0
    <3> DEFINE oneF(z) == [xx \in 1..1 |-> z]
    <3> DEFINE C1 == {z \in TraceElem : TraceCondCore(alpha, lobal, CL, himsg, oneF(z), 1)}
    <3>onev. \A z \in TraceElem : oneF(z)[1] = z  OBVIOUS
    <3>lob. lobal < B(himsg)  OBVIOUS
    <3>w. PICK rrw \in Qd(beta, himsg, 1) : \E ssw \in Tran(rrw) :
            Sig(rrw) = Sig(ssw) /\ B(ssw) = lobal /\ HasDepth(alpha, ssw, MD)
      BY <3>lob, SlowSupportWitness
    <3>w2. PICK ssw \in Tran(rrw) :
             Sig(rrw) = Sig(ssw) /\ B(ssw) = lobal /\ HasDepth(alpha, ssw, MD)
      BY <3>w
    <3>rrwM. rrw \in Messages
      <4>1. rrw \in TranExclusive(himsg)  BY <3>w, <1>hiM, <1>mi, QdProperties
      <4>2. rrw \in Tran(himsg)  BY <4>1 DEF TranExclusive
      <4> QED BY <4>2, <1>hiM, <1>mi, TranSubMessages
    <3>sswM. ssw \in Messages  BY <3>w2, <3>rrwM, <1>mi, TranSubMessages
    <3> DEFINE zw == [mm |-> himsg, rr |-> rrw, ss |-> ssw, gamma |-> beta]
    <3>zwT. zw \in TraceElem  BY <1>hiM, <3>rrwM, <3>sswM DEF TraceElem
    <3>hself. himsg \in Tran(himsg)  BY DEF Tran
    <3>zwC. zw \in C1
      <4>v. oneF(zw)[1] = zw  BY <3>zwT, <3>onev
      <4> QED BY <4>v, <3>zwT, <3>hself, <3>lob, <3>w, <3>w2 DEF TraceCondCore
    <3>ne. C1 # {}  BY <3>zwC
    <3> DEFINE M1 == {z.mm : z \in C1}
    <3>m1sub. M1 \in SUBSET Messages
      <4> SUFFICES ASSUME NEW z \in C1 PROVE z.mm \in Messages  OBVIOUS
      <4> QED BY DEF TraceElem
    <3>m1ne. M1 # {}  BY <3>ne
    <3>min. PICK mst \in M1 : \A y \in M1 : TranCard(mst) <= TranCard(y)
      BY <1>mi, <3>m1sub, <3>m1ne, ExistsMinTranCardElement
    <3>z0. PICK z0 \in C1 : z0.mm = mst  BY <3>min
    <3>z0T. z0 \in TraceElem  BY <3>z0
    <3>z0v. oneF(z0)[1] = z0  BY <3>z0T, <3>onev
    <3>z0c. TraceCondCore(alpha, lobal, CL, himsg, oneF(z0), 1)  BY <3>z0
    <3>z0f. /\ mst \in Tran(himsg)
            /\ z0.gamma \in ConFromCaught(alpha, CaughtS(CL))
            /\ lobal < B(mst)
            /\ z0.gamma \in Lrns(mst)
            /\ V(mst) = V(himsg)
      BY <3>z0c, <3>z0v, <3>z0 DEF TraceCondCore
    <3>z0L. z0.gamma \in Learners  BY <3>z0T DEF TraceElem
    <3>mstCL. mst \in CL  BY <3>z0f, <1>hiTr
    <3>mstM. mst \in Messages  BY <3>mstCL, <1>clM
    <3>rw. PICK rr1 \in Qd(z0.gamma, mst, 1) : \E ss1 \in Tran(rr1) :
             Sig(rr1) = Sig(ss1) /\ B(ss1) = lobal /\ HasDepth(alpha, ss1, MD)
      BY <3>z0f, <3>z0L, <3>mstCL, SlowSupportWitness
    <3>rw2. PICK ss1 \in Tran(rr1) :
              Sig(rr1) = Sig(ss1) /\ B(ss1) = lobal /\ HasDepth(alpha, ss1, MD)
      BY <3>rw
    <3>rr1M. rr1 \in Messages
      <4>1. rr1 \in TranExclusive(mst)  BY <3>rw, <3>mstM, <3>z0L, <1>mi, QdProperties
      <4>2. rr1 \in Tran(mst)  BY <4>1 DEF TranExclusive
      <4> QED BY <4>2, <3>mstM, <1>mi, TranSubMessages
    <3>ss1M. ss1 \in Messages  BY <3>rw2, <3>rr1M, <1>mi, TranSubMessages
    <3> DEFINE z1 == [mm |-> mst, rr |-> rr1, ss |-> ss1, gamma |-> z0.gamma]
    <3>z1T. z1 \in TraceElem  BY <3>mstM, <3>rr1M, <3>ss1M, <3>z0L DEF TraceElem
    <3> DEFINE sq1 == oneF(z1)
    <3>z1v. sq1[1] = z1  BY <3>z1T, <3>onev
    <3>core1. TraceCondCore(alpha, lobal, CL, himsg, sq1, 1)
      BY <3>z1v, <3>z0f, <3>rw, <3>rw2 DEF TraceCondCore
    <3>min1. \A z \in TraceElem :
               TraceCondCore(alpha, lobal, CL, himsg, [sq1 EXCEPT ![1] = z], 1)
                 => Cardinality(Tran(sq1[1].mm)) <= Cardinality(Tran(z.mm))
      <4> SUFFICES ASSUME NEW z \in TraceElem,
                          TraceCondCore(alpha, lobal, CL, himsg, [sq1 EXCEPT ![1] = z], 1)
                   PROVE Cardinality(Tran(mst)) <= Cardinality(Tran(z.mm))
        BY <3>z1v
      <4>v. [sq1 EXCEPT ![1] = z][1] = z  OBVIOUS
      <4>v2. oneF(z)[1] = z  BY <3>onev
      <4>x1. 1 \in Nat  OBVIOUS
      <4>c. TraceCondCore(alpha, lobal, CL, himsg, oneF(z), 1)
        BY <4>v, <4>v2, <4>x1, TraceCondCoreCongr
      <4>zin. z \in C1  BY <4>c
      <4>zmm. z.mm \in M1  BY <4>zin
      <4> QED BY <4>zmm, <3>min DEF TranCard
    <3>bud1. TraceBudgetSlow(alpha, sq1, 1)
      <4>1. MD - 1 + 1 = MD  BY <1>md
      <4> QED BY <3>z1v, <3>rw2, <4>1 DEF TraceBudgetSlow
    <3>dom. sq1 \in [1..n+1 -> TraceElem]
      <4>1. 1..n+1 = 1..1  BY <2>base
      <4>2. sq1 \in [1..1 -> TraceElem]  BY <3>z1T
      <4> QED BY <4>1, <4>2
    <3>all. \A x \in 1..n+1 :
              /\ TraceCondCoreMin(alpha, lobal, CL, himsg, sq1, x)
              /\ TraceBudgetSlow(alpha, sq1, x)
      <4> SUFFICES ASSUME NEW x \in 1..n+1
                   PROVE /\ TraceCondCoreMin(alpha, lobal, CL, himsg, sq1, x)
                         /\ TraceBudgetSlow(alpha, sq1, x)
        OBVIOUS
      <4>1. x = 1  BY <2>base
      <4> QED BY <4>1, <3>core1, <3>min1, <3>bud1 DEF TraceCondCoreMin
    <3> QED BY <3>dom, <3>all
  <2>step. CASE n >= 1
    <3>ihq. Q(n-1)
      <4>1. n - 1 \in 0..(n-1)  BY <2>step
      <4> QED BY <4>1
    <3>iharg. n - 1 \in 0..MD  BY <2>step, <1>md
    <3>arith. (n-1)+1 = n  BY <2>step
    <3>ih. PICK sq \in [1..n -> TraceElem] :
             \A x \in 1..n :
               /\ TraceCondCoreMin(alpha, lobal, CL, himsg, sq, x)
               /\ TraceBudgetSlow(alpha, sq, x)
      BY <3>ihq, <3>iharg, <3>arith DEF Q
    <3>coreAll. \A x \in 1..n : TraceCondCore(alpha, lobal, CL, himsg, sq, x)
      BY <3>ih DEF TraceCondCoreMin
    <3>tcp. /\ \A i \in 1..n : sq[i].mm \in CL /\ sq[i].rr \in CL /\ sq[i].ss \in CL
            /\ \A i, j \in 1..n : i < j => sq[j].rr \in Tran(sq[i].rr)
      <4>1. /\ \A i \in 1..n : /\ sq[i].mm \in CL
                               /\ sq[i].rr \in CL
                               /\ sq[i].ss \in CL
            /\ \A i, j \in 1..n : i < j => sq[j].rr \in Tran(sq[i].rr)
            /\ \A i, j \in 1..n : (i < j /\ j < n) =>
                 /\ Con(alpha, sq[i].rr) \subseteq Con(alpha, sq[j].rr)
                 /\ Con(alpha, sq[i].rr) # Con(alpha, sq[j].rr)
        BY <3>coreAll, TraceCoreProperties
      <4> QED BY <4>1
    <3>eltM. \A i \in 1..n : sq[i].mm \in Messages /\ sq[i].rr \in Messages /\ sq[i].ss \in Messages
      BY <3>tcp, <1>clM
    <3>eltL. \A i \in 1..n : sq[i].gamma \in Learners
      <4> SUFFICES ASSUME NEW i \in 1..n PROVE sq[i].gamma \in Learners  OBVIOUS
      <4>1. sq[i] \in TraceElem  OBVIOUS
      <4> QED BY <4>1 DEF TraceElem
    <3>ndom. n \in 1..n  BY <2>step
    <3>cn. TraceCondCore(alpha, lobal, CL, himsg, sq, n)  BY <3>coreAll, <3>ndom
    <3>i2. lobal < B(sq[n].mm)  BY <3>cn DEF TraceCondCore
    <3>i7. sq[n].gamma \in Lrns(sq[n].mm)  BY <3>cn DEF TraceCondCore
    <3>i8. sq[n].rr \in Qd(sq[n].gamma, sq[n].mm, 1)  BY <3>cn DEF TraceCondCore
    <3>i9. sq[n].ss \in Tran(sq[n].rr)  BY <3>cn DEF TraceCondCore
    <3>i13. B(sq[n].ss) = lobal  BY <3>cn DEF TraceCondCore
    <3>i14. V(sq[n].mm) = V(himsg)  BY <3>cn DEF TraceCondCore
    <3>imm. sq[n].mm \in Tran(himsg)  BY <3>cn DEF TraceCondCore
    <3>nM. sq[n].mm \in Messages /\ sq[n].rr \in Messages /\ sq[n].ss \in Messages
      BY <3>eltM, <3>ndom
    <3>nL. sq[n].gamma \in Learners  BY <3>eltL, <3>ndom
    <3>budn. HasDepth(alpha, sq[n].ss, MD - n + 1)
      <4>1. n <= MD  OBVIOUS
      <4>2. TraceBudgetSlow(alpha, sq, n)  BY <3>ih, <3>ndom
      <4> QED BY <4>1, <4>2 DEF TraceBudgetSlow
    <3>dep. MD - n + 1 \in Nat /\ MD - n + 1 >= 1  BY <1>md, <2>step
    <3>rrTE. sq[n].rr \in TranExclusive(sq[n].mm) /\ B(sq[n].rr) = B(sq[n].mm)
      BY <3>i8, <3>nM, <3>nL, <1>mi, QdProperties
    <3>gcon. sq[n].gamma \in Con(alpha, sq[n].rr)
      <4>a. CASE n = 1
        <5>1. sq[n].gamma \in ConFromCaught(alpha, CaughtS(CL))
          BY <3>cn, <4>a DEF TraceCondCore
        <5>2. sq[n].rr \in CL  BY <3>tcp, <3>ndom
        <5>3. Caught(sq[n].rr) \subseteq CaughtS(CL)  BY <5>2, <1>mi, CaughtSubClosure
        <5>4. ConFromCaught(alpha, CaughtS(CL)) \subseteq ConFromCaught(alpha, Caught(sq[n].rr))
          BY <5>3, ConFromCaughtAntitone
        <5> QED BY <5>1, <5>4 DEF Con
      <4>b. CASE n > 1
        <5>d. n - 1 \in 1..n  BY <4>b
        <5>1. sq[n].gamma \in Con(alpha, sq[n-1].rr)  BY <3>cn, <4>b DEF TraceCondCore
        <5>2. sq[n].mm \in Tran(sq[n-1].rr)  BY <3>cn, <4>b DEF TraceCondCore
        <5>3. sq[n].rr \in Tran(sq[n].mm)  BY <3>rrTE DEF TranExclusive
        <5>m. sq[n-1].rr \in Messages  BY <3>eltM, <5>d
        <5>4. Tran(sq[n].mm) \subseteq Tran(sq[n-1].rr)  BY <5>2, <5>m, <1>mi DEF TranTrans
        <5>5. sq[n].rr \in Tran(sq[n-1].rr)  BY <5>3, <5>4
        <5> QED BY <5>1, <5>5, <5>m, <1>mi, ConMonotoneTran
      <4> QED BY <4>a, <4>b, <2>step
    <3>acon. alpha \in Con(sq[n].gamma, sq[n].rr)
      <4>1. sq[n].gamma \in ConFromCaught(alpha, Caught(sq[n].rr))  BY <3>gcon DEF Con
      <4>2. alpha \in ConFromCaught(sq[n].gamma, Caught(sq[n].rr))
        BY <4>1, <3>nL, ConFromCaughtSym
      <4> QED BY <4>2 DEF Con
    <3>fr. IsOneB(sq[n].rr) /\ Fresh(sq[n].gamma, sq[n].rr)
      <4>1. IsOneB(sq[n].rr) /\ Fresh(sq[n].gamma, sq[n].rr) /\ Sig(sq[n].rr) \in Acceptors
        BY <3>i8, <3>nM, <3>nL, <1>mi, QdOneBFresh
      <4> QED BY <4>1
    <3>alrn. alpha \in Lrns(sq[n].ss)
      BY <3>budn, <3>dep, <3>nM, <1>mi, <1>lg, HasDepthLrns
    <3>vrr. V(sq[n].rr) = V(himsg)
      <4>1. V(sq[n].rr) = BalToVal(B(sq[n].mm))  BY <3>rrTE DEF V
      <4>2. V(sq[n].mm) = BalToVal(B(sq[n].mm))  BY DEF V
      <4> QED BY <4>1, <4>2, <3>i14
    <3>vne. V(sq[n].ss) # V(sq[n].rr)
      <4>1. V(sq[n].rr) = BalToVal(hibal)  BY <3>vrr, <1>vhi
      <4>2. V(sq[n].ss) = BalToVal(lobal)  BY <3>i13 DEF V
      <4> QED BY <4>1, <4>2
    <3>cap. Con(sq[n].gamma, sq[n].rr) \cap Lrns(sq[n].ss) # {}  BY <3>acon, <3>alrn
    <3>ftc. PICK p \in Tran(sq[n].rr) :
              B(p) > B(sq[n].ss) /\ V(p) = V(sq[n].rr)
              /\ Con(sq[n].gamma, sq[n].rr) \cap Lrns(p) # {}
      BY <1>mi, <3>nM, <3>nL, <3>fr, <3>i9, <3>vne, <3>cap, FreshTopConnected
    <3>pM. p \in Messages  BY <3>ftc, <3>nM, <1>mi, TranSubMessages
    <3>p2. lobal < B(p)  BY <3>ftc, <3>i13
    <3>p14. V(p) = V(himsg)  BY <3>ftc, <3>vrr
    <3>pcard. Cardinality(Tran(p)) < Cardinality(Tran(sq[n].mm))
      <4>1. Tran(p) \subseteq Tran(sq[n].rr)  BY <3>ftc, <3>nM, <1>mi DEF TranTrans
      <4>2. IsFiniteSet(Tran(sq[n].rr))  BY <3>nM, <1>mi DEF TranFinite
      <4>3. Cardinality(Tran(p)) <= Cardinality(Tran(sq[n].rr))  BY <4>1, <4>2, FS_Subset
      <4>4. Cardinality(Tran(sq[n].rr)) < Cardinality(Tran(sq[n].mm))
        BY <3>rrTE, <3>nM, <1>mi, TranExclusiveDecreasesTranSize
      <4>5. Cardinality(Tran(p)) \in Nat /\ Cardinality(Tran(sq[n].rr)) \in Nat
            /\ Cardinality(Tran(sq[n].mm)) \in Nat
        BY <3>pM, <3>nM, <1>mi, TranCardNat
      <4> QED BY <4>3, <4>4, <4>5
    <3>pTr. p \in Tran(himsg)
      <4>0. sq[n].rr \in Tran(sq[n].mm)  BY <3>rrTE DEF TranExclusive
      <4>1. Tran(sq[n].rr) \subseteq Tran(sq[n].mm)  BY <4>0, <3>nM, <1>mi DEF TranTrans
      <4>2. Tran(sq[n].mm) \subseteq Tran(himsg)  BY <3>imm, <1>hiM, <1>mi DEF TranTrans
      <4> QED BY <3>ftc, <4>1, <4>2
    <3>g. PICK gam \in Con(sq[n].gamma, sq[n].rr) \cap Lrns(p) : TRUE  BY <3>ftc
    <3>gf. gam \in Con(sq[n].gamma, sq[n].rr) /\ gam \in Lrns(p)  BY <3>g
    <3>gL. gam \in Learners  BY <3>gf DEF Con, ConFromCaught
    <3>g5. gam \in Con(alpha, sq[n].rr)
      <4>1. gam \in ConFromCaught(sq[n].gamma, Caught(sq[n].rr))  BY <3>gf DEF Con
      <4>2. sq[n].gamma \in ConFromCaught(alpha, Caught(sq[n].rr))  BY <3>gcon DEF Con
      <4>3. gam \in ConFromCaught(alpha, Caught(sq[n].rr))
        BY <1>lg, <4>1, <4>2, <3>nL, <3>gL, ConFromCaughtCondensedTrans
      <4> QED BY <4>3 DEF Con
    <3>i6. n >= 2 => gam \notin Con(alpha, sq[n-1].rr)
      <4> SUFFICES ASSUME n >= 2, gam \in Con(alpha, sq[n-1].rr) PROVE FALSE  OBVIOUS
      <4> DEFINE S == {idx \in 1..n : gam \in Con(alpha, sq[idx].rr)}
      <4>sn. S \in SUBSET Nat  OBVIOUS
      <4>nm1. n - 1 \in 1..n  OBVIOUS
      <4>ne. S # {}  BY <4>nm1
      <4>ks. PICK kst \in S : \A j \in S : kst <= j  BY <4>sn, <4>ne, ExistsLeastIndex
      <4>kf. kst \in 1..n /\ gam \in Con(alpha, sq[kst].rr)  BY <4>ks
      <4>kle. kst <= n - 1
        <5>1. n - 1 \in S  BY <4>nm1
        <5> QED BY <4>ks, <5>1
      <4>klt. kst < n /\ kst + 1 \in 1..n /\ kst >= 1  BY <4>kf, <4>kle
      <4>least. \A j \in 1..n : j < kst => gam \notin Con(alpha, sq[j].rr)
        <5> SUFFICES ASSUME NEW j \in 1..n, j < kst, gam \in Con(alpha, sq[j].rr)
                     PROVE FALSE
          OBVIOUS
        <5>1. j \in S  OBVIOUS
        <5>2. kst <= j  BY <4>ks, <5>1
        <5> QED BY <5>2
      <4>budk. HasDepth(alpha, sq[kst].ss, MD - kst + 1)
        <5>1. kst <= MD  BY <4>kf, <1>md
        <5>2. TraceBudgetSlow(alpha, sq, kst)  BY <3>ih, <4>kf
        <5> QED BY <5>1, <5>2 DEF TraceBudgetSlow
      <4>depk. MD - kst + 1 \in Nat /\ MD - kst + 1 >= 1  BY <1>md, <4>kf
      <4>ck. TraceCondCore(alpha, lobal, CL, himsg, sq, kst)  BY <3>coreAll, <4>kf
      <4>k9. sq[kst].ss \in Tran(sq[kst].rr)  BY <4>ck DEF TraceCondCore
      <4>k13. B(sq[kst].ss) = lobal  BY <4>ck DEF TraceCondCore
      <4>k8. sq[kst].rr \in Qd(sq[kst].gamma, sq[kst].mm, 1)  BY <4>ck DEF TraceCondCore
      <4>kM. sq[kst].mm \in Messages /\ sq[kst].rr \in Messages /\ sq[kst].ss \in Messages
        BY <3>eltM, <4>kf
      <4>kL. sq[kst].gamma \in Learners  BY <3>eltL, <4>kf
      <4>pk. p \in Tran(sq[kst].rr)
        <5>1. sq[n].rr \in Tran(sq[kst].rr)  BY <3>tcp, <4>kf, <4>klt, <3>ndom
        <5>2. Tran(sq[n].rr) \subseteq Tran(sq[kst].rr)  BY <5>1, <4>kM, <1>mi DEF TranTrans
        <5> QED BY <3>ftc, <5>2
      <4>tsw. PICK rrs \in Qd(gam, p, 1) : \E sss \in Qd(alpha, sq[kst].ss, MD - kst + 1) :
                Sig(rrs) = Sig(sss) /\ sss \in Tran(rrs)
        BY <4>kf, <3>gf, <4>pk, <4>k9, <4>k13, <3>p2, <4>budk, <4>depk,
           <4>kM, <3>pM, <3>gL, TraceStepWitness
      <4>tsw2. PICK sss \in Qd(alpha, sq[kst].ss, MD - kst + 1) :
                 Sig(rrs) = Sig(sss) /\ sss \in Tran(rrs)
        BY <4>tsw
      \* single-conjunct extractions: in this large context the provers
      \* handle a lemma application with an atomic goal, but not one with
      \* a conjunctive goal
      <4>sssP1. sss \in TranExclusive(sq[kst].ss)
        BY <4>tsw2, <4>kM, <1>mi, <4>depk, QdProperties
      <4>sssP2. B(sss) = B(sq[kst].ss)
        BY <4>tsw2, <4>kM, <1>mi, <4>depk, QdProperties
      <4>rrsM. rrs \in Messages
        <5>1. rrs \in TranExclusive(p)  BY <4>tsw, <3>pM, <3>gL, <1>mi, QdProperties
        <5>2. rrs \in Tran(p)  BY <5>1 DEF TranExclusive
        <5> QED BY <5>2, <3>pM, <1>mi, TranSubMessages
      <4>sssM. sss \in Messages  BY <4>tsw2, <4>rrsM, <1>mi, TranSubMessages
      <4> DEFINE wst == [mm |-> p, rr |-> rrs, ss |-> sss, gamma |-> gam]
      <4>wT. wst \in TraceElem  BY <3>pM, <4>rrsM, <4>sssM, <3>gL DEF TraceElem
      <4> DEFINE sqW == [sq EXCEPT ![kst+1] = wst]
      <4>wv. sqW[kst+1] = wst /\ sqW[kst] = sq[kst]
             /\ (kst >= 2 => sqW[kst-1] = sq[kst-1])
        BY <4>klt, <4>kf
      <4>c3. Cardinality(Tran(p)) < Cardinality(Tran(sq[kst].mm))
        <5>1. Tran(p) \subseteq Tran(sq[kst].rr)  BY <4>pk, <4>kM, <1>mi DEF TranTrans
        <5>2. IsFiniteSet(Tran(sq[kst].rr))  BY <4>kM, <1>mi DEF TranFinite
        <5>3. Cardinality(Tran(p)) <= Cardinality(Tran(sq[kst].rr))  BY <5>1, <5>2, FS_Subset
        <5>4. sq[kst].rr \in TranExclusive(sq[kst].mm)
          <6>1. sq[kst].rr \in TranExclusive(sq[kst].mm) /\ B(sq[kst].rr) = B(sq[kst].mm)
            BY <4>k8, <4>kM, <4>kL, <1>mi, QdProperties
          <6> QED BY <6>1
        <5>5. Cardinality(Tran(sq[kst].rr)) < Cardinality(Tran(sq[kst].mm))
          BY <5>4, <4>kM, <1>mi, TranExclusiveDecreasesTranSize
        <5>6. Cardinality(Tran(p)) \in Nat /\ Cardinality(Tran(sq[kst].rr)) \in Nat
              /\ Cardinality(Tran(sq[kst].mm)) \in Nat
          BY <3>pM, <4>kM, <1>mi, TranCardNat
        <5> QED BY <5>3, <5>5, <5>6
      <4>c6. kst + 1 > 2 => gam \notin Con(alpha, sq[kst-1].rr)
        <5> SUFFICES ASSUME kst + 1 > 2 PROVE gam \notin Con(alpha, sq[kst-1].rr)
          OBVIOUS
        <5>1. kst >= 2  OBVIOUS
        <5>2. kst - 1 \in 1..n /\ kst - 1 < kst  BY <5>1, <4>kf
        <5> QED BY <4>least, <5>2
      <4>coreW. TraceCondCore(alpha, lobal, CL, himsg, sqW, kst+1)
        <5>arith. (kst+1) - 1 = kst /\ (kst+1) - 2 = kst - 1 /\ kst + 1 > 1 /\ kst + 1 # 1
          BY <4>klt
        <5>s10. sss \in Tran(sq[kst].ss)  BY <4>sssP1 DEF TranExclusive
        <5>s13. B(sss) = lobal  BY <4>sssP2, <4>k13
        <5> QED BY <5>arith, <4>wv, <3>pTr, <3>p2, <4>c3, <4>pk, <4>kf, <4>c6,
                   <3>gf, <4>tsw, <4>tsw2, <5>s10, <5>s13, <3>p14
                DEF TraceCondCore
      <4>minK. TraceCondCoreMin(alpha, lobal, CL, himsg, sq, kst+1)  BY <3>ih, <4>klt
      <4>le. Cardinality(Tran(sq[kst+1].mm)) <= Cardinality(Tran(wst.mm))
        BY <4>minK, <4>wT, <4>coreW DEF TraceCondCoreMin
      <4>wmm. wst.mm = p  OBVIOUS
      <4>lt. Cardinality(Tran(p)) < Cardinality(Tran(sq[kst+1].mm))
        <5>k1. kst + 1 \in 1..n  BY <4>klt
        <5>ck1. TraceCondCore(alpha, lobal, CL, himsg, sq, kst+1)  BY <3>coreAll, <5>k1
        <5>k18. sq[kst+1].rr \in Qd(sq[kst+1].gamma, sq[kst+1].mm, 1)  BY <5>ck1 DEF TraceCondCore
        <5>k1M. sq[kst+1].mm \in Messages /\ sq[kst+1].rr \in Messages  BY <3>eltM, <5>k1
        <5>k1L. sq[kst+1].gamma \in Learners  BY <3>eltL, <5>k1
        <5>te. sq[kst+1].rr \in TranExclusive(sq[kst+1].mm)
          <6>1. sq[kst+1].rr \in TranExclusive(sq[kst+1].mm)
                /\ B(sq[kst+1].rr) = B(sq[kst+1].mm)
            BY <5>k18, <5>k1M, <5>k1L, <1>mi, QdProperties
          <6> QED BY <6>1
        <5>pk1. p \in Tran(sq[kst+1].rr)
          <6>a. CASE kst + 1 = n
            <7> QED BY <3>ftc, <6>a
          <6>b. CASE kst + 1 < n
            <7>1. sq[n].rr \in Tran(sq[kst+1].rr)  BY <3>tcp, <5>k1, <6>b, <3>ndom
            <7>2. Tran(sq[n].rr) \subseteq Tran(sq[kst+1].rr)  BY <7>1, <5>k1M, <1>mi DEF TranTrans
            <7> QED BY <3>ftc, <7>2
          <6> QED BY <6>a, <6>b, <4>klt
        <5>c1. Tran(p) \subseteq Tran(sq[kst+1].rr)  BY <5>pk1, <5>k1M, <1>mi DEF TranTrans
        <5>c2. IsFiniteSet(Tran(sq[kst+1].rr))  BY <5>k1M, <1>mi DEF TranFinite
        <5>c3. Cardinality(Tran(p)) <= Cardinality(Tran(sq[kst+1].rr))  BY <5>c1, <5>c2, FS_Subset
        <5>c4. Cardinality(Tran(sq[kst+1].rr)) < Cardinality(Tran(sq[kst+1].mm))
          BY <5>te, <5>k1M, <1>mi, TranExclusiveDecreasesTranSize
        <5>ty. Cardinality(Tran(p)) \in Nat /\ Cardinality(Tran(sq[kst+1].rr)) \in Nat
               /\ Cardinality(Tran(sq[kst+1].mm)) \in Nat
          BY <3>pM, <5>k1M, <1>mi, TranCardNat
        <5> QED BY <5>c3, <5>c4, <5>ty
      <4>ty2. Cardinality(Tran(p)) \in Nat /\ Cardinality(Tran(sq[kst+1].mm)) \in Nat
        <5>1. sq[kst+1].mm \in Messages  BY <3>eltM, <4>klt
        <5> QED BY <3>pM, <5>1, <1>mi, TranCardNat
      <4> QED BY <4>le, <4>wmm, <4>lt, <4>ty2
    <3>tswN. PICK rrp \in Qd(gam, p, 1) : \E ssp \in Qd(alpha, sq[n].ss, MD - n + 1) :
               Sig(rrp) = Sig(ssp) /\ ssp \in Tran(rrp)
      BY <3>g5, <3>gf, <3>ftc, <3>i9, <3>i13, <3>p2, <3>budn, <3>dep,
         <3>nM, <3>pM, <3>gL, TraceStepWitness
    <3>tswN2. PICK ssp \in Qd(alpha, sq[n].ss, MD - n + 1) :
                Sig(rrp) = Sig(ssp) /\ ssp \in Tran(rrp)
      BY <3>tswN
    <3>sspP1. ssp \in TranExclusive(sq[n].ss)
      BY <3>tswN2, <3>nM, <1>mi, <3>dep, QdProperties
    <3>sspP2. B(ssp) = B(sq[n].ss)
      BY <3>tswN2, <3>nM, <1>mi, <3>dep, QdProperties
    <3>rrpM. rrp \in Messages
      <4>1. rrp \in TranExclusive(p)  BY <3>tswN, <3>pM, <3>gL, <1>mi, QdProperties
      <4>2. rrp \in Tran(p)  BY <4>1 DEF TranExclusive
      <4> QED BY <4>2, <3>pM, <1>mi, TranSubMessages
    <3>sspM. ssp \in Messages  BY <3>tswN2, <3>rrpM, <1>mi, TranSubMessages
    <3> DEFINE seqE(z) == [xx \in 1..n+1 |-> IF xx = n+1 THEN z ELSE sq[xx]]
    <3>seqEv. \A z \in TraceElem :
                seqE(z)[n+1] = z /\ (\A xx \in 1..n : seqE(z)[xx] = sq[xx])
      OBVIOUS
    <3> DEFINE zp == [mm |-> p, rr |-> rrp, ss |-> ssp, gamma |-> gam]
    <3>zpT. zp \in TraceElem  BY <3>pM, <3>rrpM, <3>sspM, <3>gL DEF TraceElem
    <3>zpC. TraceCondCore(alpha, lobal, CL, himsg, seqE(zp), n+1)
      <4>arith. (n+1) - 1 = n /\ (n+1) - 2 = n - 1 /\ n + 1 > 1 /\ n + 1 # 1
                /\ (n + 1 > 2 <=> n >= 2)
        BY <2>step
      <4>v. seqE(zp)[n+1] = zp /\ seqE(zp)[n] = sq[n]
            /\ (n >= 2 => seqE(zp)[n-1] = sq[n-1])
        BY <3>zpT, <3>seqEv, <2>step
      <4>s10. ssp \in Tran(sq[n].ss)  BY <3>sspP1 DEF TranExclusive
      <4>s13. B(ssp) = lobal  BY <3>sspP2, <3>i13
      <4> QED BY <4>arith, <4>v, <3>pTr, <3>p2, <3>pcard, <3>ftc, <3>g5, <3>i6,
                 <3>gf, <3>tswN, <3>tswN2, <4>s10, <4>s13, <3>p14
              DEF TraceCondCore
    <3> DEFINE CC == {z \in TraceElem : TraceCondCore(alpha, lobal, CL, himsg, seqE(z), n+1)}
    <3>ccne. zp \in CC  BY <3>zpC, <3>zpT
    <3> DEFINE MM == {z.mm : z \in CC}
    <3>mmsub. MM \in SUBSET Messages
      <4> SUFFICES ASSUME NEW z \in CC PROVE z.mm \in Messages  OBVIOUS
      <4> QED BY DEF TraceElem
    <3>mmne. MM # {}  BY <3>ccne
    <3>minP. PICK mst \in MM : \A y \in MM : TranCard(mst) <= TranCard(y)
      BY <1>mi, <3>mmsub, <3>mmne, ExistsMinTranCardElement
    <3>zz0. PICK z0 \in CC : z0.mm = mst  BY <3>minP
    <3>z0C. TraceCondCore(alpha, lobal, CL, himsg, seqE(z0), n+1)  BY <3>zz0
    <3>z0T. z0 \in TraceElem  BY <3>zz0
    <3>z0L2. z0.gamma \in Learners  BY <3>z0T DEF TraceElem
    <3>z0v. seqE(z0)[n+1] = z0 /\ seqE(z0)[n] = sq[n]
            /\ (n >= 2 => seqE(z0)[n-1] = sq[n-1])
      BY <3>z0T, <3>seqEv, <2>step
    <3>z0f. /\ mst \in Tran(himsg)
            /\ lobal < B(mst)
            /\ Cardinality(Tran(mst)) < Cardinality(Tran(sq[n].mm))
            /\ mst \in Tran(sq[n].rr)
            /\ z0.gamma \in Con(alpha, sq[n].rr)
            /\ (n >= 2 => z0.gamma \notin Con(alpha, sq[n-1].rr))
            /\ z0.gamma \in Lrns(mst)
            /\ V(mst) = V(himsg)
      <4>arith. (n+1) - 1 = n /\ (n+1) - 2 = n - 1 /\ n + 1 > 1
                /\ (n + 1 > 2 <=> n >= 2)
        BY <2>step
      <4> QED BY <3>z0C, <3>z0v, <3>zz0, <4>arith DEF TraceCondCore
    <3>mstM2. mst \in Messages  BY <3>zz0, <3>mmsub
    <3>rwN. PICK rrf \in Qd(z0.gamma, mst, 1) : \E ssf \in Qd(alpha, sq[n].ss, MD - n + 1) :
              Sig(rrf) = Sig(ssf) /\ ssf \in Tran(rrf)
      BY <3>z0f, <3>i9, <3>i13, <3>budn, <3>dep, <3>nM, <3>mstM2, <3>z0L2,
         TraceStepWitness
    <3>rwN2. PICK ssf \in Qd(alpha, sq[n].ss, MD - n + 1) :
               Sig(rrf) = Sig(ssf) /\ ssf \in Tran(rrf)
      BY <3>rwN
    <3>ssfP1. ssf \in TranExclusive(sq[n].ss)
      BY <3>rwN2, <3>nM, <1>mi, <3>dep, QdProperties
    <3>ssfP2. B(ssf) = B(sq[n].ss)
      BY <3>rwN2, <3>nM, <1>mi, <3>dep, QdProperties
    <3>ssfP3. HasDepth(alpha, ssf, MD - n + 1 - 1)
      <4>1. ssf \in Qd(alpha, sq[n].ss, MD - n + 1)  BY <3>rwN2
      \* NB: binary - binds tighter than + in TLA+, so the goal's
      \* MD - n + 1 - 1 parses as (MD-n) + (1-1), NOT ((MD-n)+1) - 1;
      \* the equality is arithmetic (needs MD, n \in Nat), not reflexivity.
      <4>e. MD - n + 1 - 1 = (MD - n + 1) - 1  BY <1>md
      <4> QED BY <4>1, <4>e, <3>nM, <1>mi, <3>dep, QdDepthMember
    <3>rrfM. rrf \in Messages
      <4>1. rrf \in TranExclusive(mst)  BY <3>rwN, <3>mstM2, <3>z0L2, <1>mi, QdProperties
      <4>2. rrf \in Tran(mst)  BY <4>1 DEF TranExclusive
      <4> QED BY <4>2, <3>mstM2, <1>mi, TranSubMessages
    <3>ssfM. ssf \in Messages  BY <3>rwN2, <3>rrfM, <1>mi, TranSubMessages
    <3> DEFINE zf == [mm |-> mst, rr |-> rrf, ss |-> ssf, gamma |-> z0.gamma]
    <3>zfT. zf \in TraceElem  BY <3>mstM2, <3>rrfM, <3>ssfM, <3>z0L2 DEF TraceElem
    <3> DEFINE sqN == seqE(zf)
    <3>zfv. sqN[n+1] = zf /\ sqN[n] = sq[n] /\ (\A xx \in 1..n : sqN[xx] = sq[xx])
            /\ (n >= 2 => sqN[n-1] = sq[n-1])
      BY <3>zfT, <3>seqEv, <2>step
    <3>zfC. TraceCondCore(alpha, lobal, CL, himsg, sqN, n+1)
      <4>arith. (n+1) - 1 = n /\ (n+1) - 2 = n - 1 /\ n + 1 > 1 /\ n + 1 # 1
                /\ (n + 1 > 2 <=> n >= 2)
        BY <2>step
      <4>s10. ssf \in Tran(sq[n].ss)  BY <3>ssfP1 DEF TranExclusive
      <4>s13. B(ssf) = lobal  BY <3>ssfP2, <3>i13
      <4> QED BY <4>arith, <3>zfv, <3>z0f, <3>rwN, <3>rwN2, <4>s10, <4>s13
              DEF TraceCondCore
    <3>domN. sqN \in [1..n+1 -> TraceElem]
      <4> SUFFICES ASSUME NEW xx \in 1..n+1 PROVE sqN[xx] \in TraceElem  OBVIOUS
      <4>a. CASE xx = n+1  BY <4>a, <3>zfT, <3>zfv
      <4>b. CASE xx # n+1
        <5>1. xx \in 1..n  BY <4>b
        <5>2. sqN[xx] = sq[xx]  BY <5>1, <3>zfv
        <5> QED BY <5>1, <5>2
      <4> QED BY <4>a, <4>b
    <3>minN. \A z \in TraceElem :
               TraceCondCore(alpha, lobal, CL, himsg, [sqN EXCEPT ![n+1] = z], n+1)
                 => Cardinality(Tran(sqN[n+1].mm)) <= Cardinality(Tran(z.mm))
      <4> SUFFICES ASSUME NEW z \in TraceElem,
                          TraceCondCore(alpha, lobal, CL, himsg, [sqN EXCEPT ![n+1] = z], n+1)
                   PROVE Cardinality(Tran(mst)) <= Cardinality(Tran(z.mm))
        BY <3>zfv
      <4>v. [sqN EXCEPT ![n+1] = z][n+1] = z
            /\ [sqN EXCEPT ![n+1] = z][n] = sq[n]
            /\ (n >= 2 => [sqN EXCEPT ![n+1] = z][n-1] = sq[n-1])
        BY <3>zfv, <2>step
      <4>v2. seqE(z)[n+1] = z /\ seqE(z)[n] = sq[n]
             /\ (n >= 2 => seqE(z)[n-1] = sq[n-1])
        BY <3>seqEv, <2>step
      <4>arith. (n+1) - 1 = n /\ (n+1) - 2 = n - 1 /\ n + 1 \in Nat
                /\ (n + 1 > 2 <=> n >= 2)
        BY <2>step
      <4>cg. TraceCondCore(alpha, lobal, CL, himsg, seqE(z), n+1)
        BY <4>v, <4>v2, <4>arith, TraceCondCoreCongr
      <4>zin. z \in CC  BY <4>cg
      <4>zmm. z.mm \in MM  BY <4>zin
      <4> QED BY <4>zmm, <3>minP DEF TranCard
    <3>budN. TraceBudgetSlow(alpha, sqN, n+1)
      <4> SUFFICES ASSUME n+1 <= MD
                   PROVE HasDepth(alpha, sqN[n+1].ss, MD - (n+1) + 1)
        BY DEF TraceBudgetSlow
      <4>1. sqN[n+1].ss = ssf  BY <3>zfv
      <4>2. MD - (n+1) + 1 = MD - n + 1 - 1  BY <1>md, <2>step
      <4> QED BY <4>1, <4>2, <3>ssfP3
    <3>old. \A x \in 1..n :
              /\ TraceCondCoreMin(alpha, lobal, CL, himsg, sqN, x)
              /\ TraceBudgetSlow(alpha, sqN, x)
      <4> SUFFICES ASSUME NEW x \in 1..n
                   PROVE /\ TraceCondCoreMin(alpha, lobal, CL, himsg, sqN, x)
                         /\ TraceBudgetSlow(alpha, sqN, x)
        OBVIOUS
      <4>xN. x \in Nat  OBVIOUS
      <4>vals. sqN[x] = sq[x] /\ (x > 1 => sqN[x-1] = sq[x-1]) /\ (x > 2 => sqN[x-2] = sq[x-2])
        <5>1. sqN[x] = sq[x]  BY <3>zfv
        <5>2. x > 1 => sqN[x-1] = sq[x-1]
          <6> SUFFICES ASSUME x > 1 PROVE sqN[x-1] = sq[x-1]  OBVIOUS
          <6>1. x - 1 \in 1..n  OBVIOUS
          <6> QED BY <6>1, <3>zfv
        <5>3. x > 2 => sqN[x-2] = sq[x-2]
          <6> SUFFICES ASSUME x > 2 PROVE sqN[x-2] = sq[x-2]  OBVIOUS
          <6>1. x - 2 \in 1..n  OBVIOUS
          <6> QED BY <6>1, <3>zfv
        <5> QED BY <5>1, <5>2, <5>3
      <4>core. TraceCondCore(alpha, lobal, CL, himsg, sqN, x)
        BY <3>coreAll, <4>vals, <4>xN, TraceCondCoreCongr
      <4>minx. \A z \in TraceElem :
                 TraceCondCore(alpha, lobal, CL, himsg, [sqN EXCEPT ![x] = z], x)
                   => Cardinality(Tran(sqN[x].mm)) <= Cardinality(Tran(z.mm))
        <5> SUFFICES ASSUME NEW z \in TraceElem,
                            TraceCondCore(alpha, lobal, CL, himsg, [sqN EXCEPT ![x] = z], x)
                     PROVE Cardinality(Tran(sq[x].mm)) <= Cardinality(Tran(z.mm))
          BY <4>vals
        <5>v1. [sqN EXCEPT ![x] = z][x] = z /\ [sq EXCEPT ![x] = z][x] = z  OBVIOUS
        <5>v2. x > 1 => ([sqN EXCEPT ![x] = z][x-1] = sq[x-1]
                         /\ [sq EXCEPT ![x] = z][x-1] = sq[x-1])
          <6> SUFFICES ASSUME x > 1 PROVE [sqN EXCEPT ![x] = z][x-1] = sq[x-1]
                                          /\ [sq EXCEPT ![x] = z][x-1] = sq[x-1]
            OBVIOUS
          <6>1. x - 1 \in 1..n /\ x - 1 # x  OBVIOUS
          <6> QED BY <6>1, <3>zfv
        <5>v3. x > 2 => ([sqN EXCEPT ![x] = z][x-2] = sq[x-2]
                         /\ [sq EXCEPT ![x] = z][x-2] = sq[x-2])
          <6> SUFFICES ASSUME x > 2 PROVE [sqN EXCEPT ![x] = z][x-2] = sq[x-2]
                                          /\ [sq EXCEPT ![x] = z][x-2] = sq[x-2]
            OBVIOUS
          <6>1. x - 2 \in 1..n /\ x - 2 # x  OBVIOUS
          <6> QED BY <6>1, <3>zfv
        <5>cg. TraceCondCore(alpha, lobal, CL, himsg, [sq EXCEPT ![x] = z], x)
          BY <5>v1, <5>v2, <5>v3, <4>xN, TraceCondCoreCongr
        <5>ihm. TraceCondCoreMin(alpha, lobal, CL, himsg, sq, x)  BY <3>ih
        <5> QED BY <5>ihm, <5>cg DEF TraceCondCoreMin
      <4>budx. TraceBudgetSlow(alpha, sqN, x)
        <5>1. sqN[x].ss = sq[x].ss  BY <4>vals
        <5>2. TraceBudgetSlow(alpha, sq, x)  BY <3>ih
        <5> QED BY <5>1, <5>2 DEF TraceBudgetSlow
      <4> QED BY <4>core, <4>minx, <4>budx DEF TraceCondCoreMin
    <3>all. \A x \in 1..n+1 :
              /\ TraceCondCoreMin(alpha, lobal, CL, himsg, sqN, x)
              /\ TraceBudgetSlow(alpha, sqN, x)
      <4> SUFFICES ASSUME NEW x \in 1..n+1
                   PROVE /\ TraceCondCoreMin(alpha, lobal, CL, himsg, sqN, x)
                         /\ TraceBudgetSlow(alpha, sqN, x)
        OBVIOUS
      <4>a. CASE x \in 1..n  BY <3>old, <4>a
      <4>b. CASE x = n+1
        BY <3>zfC, <3>minN, <3>budN, <4>b DEF TraceCondCoreMin
      <4> QED BY <4>a, <4>b
    <3> QED BY <3>domN, <3>all
  <2> QED BY <2>base, <2>step
<1> QED BY <1>ind, GeneralNatInduction, IsaM("blast")

\* (A fast-decision trace-existence lemma, TraceExistenceFast, stood here
\* OMITTED until 2026-07-16, when the "connectivity laundering" countermodel
\* -- TLCLaunder.tla + XFastCE3Graph.tla, see DecisionFastSoundness.md --
\* showed it FALSE and DecisionFast unsound; the fast path was then dropped
\* from Decision.)

\* --- assembly ------------------------------------------------------

\* Different ballots agree (hpaxos-tla ChosenSafeCaseLt): extract himsg from
\* the high decision (DecisionHighWitness); the (slow) low decision gives
\* TraceExistenceSlow; instantiate at i = MaxDepth(alpha) and conclude by
\* TraceContradiction.
LEMMA AgreementCaseLt ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions,
         ValueInterfaceAssumptions,
         NEW mset \in SUBSET Messages,
         NEW alpha \in Learners, NEW beta \in Learners,
         NEW lobal \in Ballots, NEW hibal \in Ballots,
         lobal < hibal,
         Decision(mset, alpha, lobal),
         Decision(mset, beta, hibal),
         beta \in ConFromCaught(alpha, CaughtS(TranClosure(mset)))
  PROVE BalToVal(lobal) = BalToVal(hibal)
<1> SUFFICES ASSUME BalToVal(lobal) # BalToVal(hibal) PROVE FALSE  OBVIOUS
<1>lg. FiniteAcceptors /\ LearnersNonEmpty /\ QuorumsNonEmpty
       /\ LearnersMightAgree /\ ValidLearnerGraphAssumption
  BY DEF LearnerGraphAssumptions
<1>md. MaxDepth(alpha) \in Nat
  <2>1. MaxDepth(alpha) \in 1..Cardinality(Acceptors)  BY <1>lg, MaxDepthFiniteAcceptors
  <2> QED BY <2>1
<1>mdin. MaxDepth(alpha) \in 0..MaxDepth(alpha)  BY <1>md
<1>hw. PICK himsg \in TranClosure(mset) : B(himsg) = hibal /\ beta \in Lrns(himsg)
  BY DecisionHighWitness
<1>slow. CASE DecisionSlow(mset, alpha, lobal)
  <2>ex. \A i \in 0..MaxDepth(alpha) :
           \E seq \in [1..i+1 -> TraceElem] :
             \A x \in 1..i+1 :
               /\ TraceCondCoreMin(alpha, lobal, TranClosure(mset), himsg, seq, x)
               /\ TraceBudgetSlow(alpha, seq, x)
    BY <1>slow, <1>hw, TraceExistenceSlow
  <2>pick. PICK seq \in [1..MaxDepth(alpha)+1 -> TraceElem] :
             \A x \in 1..MaxDepth(alpha)+1 :
               /\ TraceCondCoreMin(alpha, lobal, TranClosure(mset), himsg, seq, x)
               /\ TraceBudgetSlow(alpha, seq, x)
    BY <2>ex, <1>mdin
  <2>coremin. \A x \in 1..MaxDepth(alpha)+1 :
                TraceCondCoreMin(alpha, lobal, TranClosure(mset), himsg, seq, x)
    BY <2>pick
  <2> QED BY <2>coremin, TraceContradiction
<1> QED BY <1>slow DEF Decision

\* AgreementM assembles by trichotomy on the ballots: equal ballots agree
\* definitionally (values are a function of the ballot); alphabal < betabal
\* is AgreementCaseLt with the connection hypothesis reoriented by
\* ConFromCaughtSym; betabal < alphabal is AgreementCaseLt with the roles
\* swapped.
LEMMA AgreementM ==
  (/\ MessageInterfaceAssumptions
   /\ LearnerGraphAssumptions
   /\ ValueInterfaceAssumptions) =>
    \A alpha \in Learners :
    \A beta \in Learners :
    \A m \in SUBSET Messages :
    \A alphabal \in Ballots :
    \A betabal \in Ballots :
    (/\ Decision(m, alpha, alphabal)
     /\ Decision(m, beta,  betabal )
     /\ alpha \in ConFromCaught(beta, CaughtS(TranClosure(m)))
    )=> BalToVal(alphabal) = BalToVal(betabal)
<1> SUFFICES ASSUME MessageInterfaceAssumptions,
                    LearnerGraphAssumptions,
                    ValueInterfaceAssumptions,
                    NEW alpha \in Learners, NEW beta \in Learners,
                    NEW m \in SUBSET Messages,
                    NEW alphabal \in Ballots, NEW betabal \in Ballots,
                    Decision(m, alpha, alphabal),
                    Decision(m, beta, betabal),
                    alpha \in ConFromCaught(beta, CaughtS(TranClosure(m)))
             PROVE BalToVal(alphabal) = BalToVal(betabal)
  OBVIOUS
<1>sym. beta \in ConFromCaught(alpha, CaughtS(TranClosure(m)))
  BY ConFromCaughtSym
<1>a. CASE alphabal < betabal
  <2> QED BY <1>a, <1>sym, AgreementCaseLt
<1>b. CASE betabal < alphabal
  <2>1. BalToVal(betabal) = BalToVal(alphabal)  BY <1>b, AgreementCaseLt
  <2> QED BY <2>1
<1>c. CASE alphabal = betabal
  <2> QED BY <1>c
<1>tri. alphabal < betabal \/ betabal < alphabal \/ alphabal = betabal
  BY DEF Ballots
<1> QED BY <1>a, <1>b, <1>c, <1>tri


\* (if alpha is still connected to alpha)
\* for any set of messages (with ballot less than bal) that will ever be sent
\* there is a proposal p with ballot > bal such that all acceptors
\*  (who are not caught) can make a fresh 1b
\*
\* Proving this may require creating a (finite) subset of m that are 2as at each ballot with every possible signer and set of learners. 
\*
\* Notes on ensuring this happens in an actual implementation (not this spec):
\* You could (after some time) adopt a communication pattern where
\*  SafeAcceptors only listen to messages forwarded by the leader.
\* Therefore, if you have a safe leader, and it waits long enough,
\*  and every SafeAcceptor forwards everything it knows to the leader,
\*  you will eventually arrive at a time when the leader knows m, the 
\*  set of all messages any SafeAcceptor knows. 
\* This actually would make m finite, which oddly enough, we don't 
\*  actually require below. 
IdOp(n) == n

\* FiniteMaxExists cannot be applied directly to a locally-DEFINEd set (same
\* issue documented at BMaxExists/TranMaxExists) -- wrap it once for an
\* opaque NEW T so call sites can cite this instead.
LEMMA NatMaxExists ==
  ASSUME NEW T \in SUBSET Nat, IsFiniteSet(T), T # {}
  PROVE \E r \in T : \A y \in T : y <= r
<1>1. \A z \in T : IdOp(z) \in Nat  BY DEF IdOp
<1>2. \E r \in T : \A y \in T : IdOp(y) <= IdOp(r)  BY <1>1, FiniteMaxExists
<1> QED BY <1>2 DEF IdOp

\* Generic: among candidates satisfying P within TranClosure(mm), all with
\* ballot < bd, there is a ballot-maximal one.  Works even if TranClosure(mm)
\* itself is infinite -- only the ACHIEVED BALLOT VALUES need be bounded.
LEMMA MaxBWitness ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, AlwaysAProposal,
         NEW mm \in SUBSET Messages, NEW bd \in Nat, NEW P(_),
         \A x \in TranClosure(mm) : B(x) < bd,
         \E x \in TranClosure(mm) : P(x)
  PROVE \E x \in TranClosure(mm) :
          P(x) /\ (\A y \in TranClosure(mm) : P(y) => B(y) <= B(x))
<1> DEFINE Cand == {x \in TranClosure(mm) : P(x)}
<1> DEFINE Bals == {B(x) : x \in Cand}
<1>ne. Cand # {}  OBVIOUS
<1>candmsg. Cand \subseteq Messages
  <2> SUFFICES ASSUME NEW z \in Cand PROVE z \in Messages  OBVIOUS
  <2>0. z \in TranClosure(mm)  OBVIOUS
  <2> QED BY <2>0, TranClosureClosed
<1>balssub. Bals \subseteq 0..bd
  <2> SUFFICES ASSUME NEW w \in Bals PROVE w \in 0..bd  OBVIOUS
  <2>1. PICK z \in Cand : w = B(z)  OBVIOUS
  <2>2. z \in TranClosure(mm)  BY <2>1
  <2>3. B(z) \in Ballots  BY <2>1, <1>candmsg, BBallot
  <2>4. B(z) \in Nat  BY <2>3 DEF Ballots
  <2>5. B(z) < bd  BY <2>2
  <2> QED BY <2>1, <2>4, <2>5
<1>balsfin. IsFiniteSet(Bals)
  <2>1. IsFiniteSet(0..bd)  BY FS_Interval
  <2> QED BY <2>1, <1>balssub, FS_Subset
<1>balsne. Bals # {}  BY <1>ne
<1>balssubnat. Bals \subseteq Nat  BY <1>balssub
<1>maxex. \E r \in Bals : \A y \in Bals : y <= r
  BY <1>balsfin, <1>balsne, <1>balssubnat, NatMaxExists
<1> PICK hibal \in Bals : \A y \in Bals : y <= hibal  BY <1>maxex
<1> PICK x \in Cand : B(x) = hibal  OBVIOUS
<1>xTC. x \in TranClosure(mm) /\ P(x)  OBVIOUS
<1>xmax. \A y \in TranClosure(mm) : P(y) => B(y) <= B(x)
  <2> SUFFICES ASSUME NEW y \in TranClosure(mm), P(y) PROVE B(y) <= B(x)  OBVIOUS
  <2>1. y \in Cand  OBVIOUS
  <2>2. B(y) \in Bals  BY <2>1
  <2> QED BY <2>2
<1> QED BY <1>xTC, <1>xmax

\* --- per-acceptor top witness (concrete predicate, no higher-order citation) ---
TopAcceptorMsg(mm, s) ==
  CHOOSE x \in TranClosure(mm) :
    Sig(x) = s /\ (\A y \in TranClosure(mm) : Sig(y) = s => B(y) <= B(x))

LEMMA TopAcceptorMsgCorrect ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, AlwaysAProposal,
         NEW mm \in SUBSET Messages, NEW bd \in Nat, NEW s,
         \A x \in TranClosure(mm) : B(x) < bd,
         \E x \in TranClosure(mm) : Sig(x) = s
  PROVE /\ TopAcceptorMsg(mm, s) \in TranClosure(mm)
        /\ Sig(TopAcceptorMsg(mm, s)) = s
        /\ \A y \in TranClosure(mm) : Sig(y) = s => B(y) <= B(TopAcceptorMsg(mm, s))
<1> DEFINE Cand == {x \in TranClosure(mm) : Sig(x) = s}
<1> DEFINE Bals == {B(x) : x \in Cand}
<1>ne. Cand # {}  OBVIOUS
<1>candmsg. Cand \subseteq Messages
  <2> SUFFICES ASSUME NEW z \in Cand PROVE z \in Messages  OBVIOUS
  <2>0. z \in TranClosure(mm)  OBVIOUS
  <2> QED BY <2>0, TranClosureClosed
<1>balssub. Bals \subseteq 0..bd
  <2> SUFFICES ASSUME NEW w \in Bals PROVE w \in 0..bd  OBVIOUS
  <2>1. PICK z \in Cand : w = B(z)  OBVIOUS
  <2>2. z \in TranClosure(mm)  BY <2>1
  <2>3. B(z) \in Ballots  BY <2>1, <1>candmsg, BBallot
  <2>4. B(z) \in Nat  BY <2>3 DEF Ballots
  <2>5. B(z) < bd  BY <2>2
  <2> QED BY <2>1, <2>4, <2>5
<1>balsfin. IsFiniteSet(Bals)
  <2>1. IsFiniteSet(0..bd)  BY FS_Interval
  <2> QED BY <2>1, <1>balssub, FS_Subset
<1>balsne. Bals # {}  BY <1>ne
<1>balssubnat. Bals \subseteq Nat  BY <1>balssub
<1>maxex. \E r \in Bals : \A y \in Bals : y <= r
  BY <1>balsfin, <1>balsne, <1>balssubnat, NatMaxExists
<1> PICK hibal \in Bals : \A y \in Bals : y <= hibal  BY <1>maxex
<1> PICK x \in Cand : B(x) = hibal  OBVIOUS
<1>xTC. x \in TranClosure(mm) /\ Sig(x) = s  OBVIOUS
<1>xmax. \A y \in TranClosure(mm) : Sig(y) = s => B(y) <= B(x)
  <2> SUFFICES ASSUME NEW y \in TranClosure(mm), Sig(y) = s PROVE B(y) <= B(x)  OBVIOUS
  <2>1. y \in Cand  OBVIOUS
  <2>2. B(y) \in Bals  BY <2>1
  <2> QED BY <2>2
<1> QED BY <1>xTC, <1>xmax DEF TopAcceptorMsg

\* --- per-learner top witness (concrete predicate) ---
TopLearnerMsg(mm, beta) ==
  CHOOSE x \in TranClosure(mm) :
    beta \in Lrns(x) /\ (\A y \in TranClosure(mm) : beta \in Lrns(y) => B(y) <= B(x))

LEMMA TopLearnerMsgCorrect ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, AlwaysAProposal,
         NEW mm \in SUBSET Messages, NEW bd \in Nat, NEW beta,
         \A x \in TranClosure(mm) : B(x) < bd,
         \E x \in TranClosure(mm) : beta \in Lrns(x)
  PROVE /\ TopLearnerMsg(mm, beta) \in TranClosure(mm)
        /\ beta \in Lrns(TopLearnerMsg(mm, beta))
        /\ \A y \in TranClosure(mm) : beta \in Lrns(y) => B(y) <= B(TopLearnerMsg(mm, beta))
<1> DEFINE Cand == {x \in TranClosure(mm) : beta \in Lrns(x)}
<1> DEFINE Bals == {B(x) : x \in Cand}
<1>ne. Cand # {}  OBVIOUS
<1>candmsg. Cand \subseteq Messages
  <2> SUFFICES ASSUME NEW z \in Cand PROVE z \in Messages  OBVIOUS
  <2>0. z \in TranClosure(mm)  OBVIOUS
  <2> QED BY <2>0, TranClosureClosed
<1>balssub. Bals \subseteq 0..bd
  <2> SUFFICES ASSUME NEW w \in Bals PROVE w \in 0..bd  OBVIOUS
  <2>1. PICK z \in Cand : w = B(z)  OBVIOUS
  <2>2. z \in TranClosure(mm)  BY <2>1
  <2>3. B(z) \in Ballots  BY <2>1, <1>candmsg, BBallot
  <2>4. B(z) \in Nat  BY <2>3 DEF Ballots
  <2>5. B(z) < bd  BY <2>2
  <2> QED BY <2>1, <2>4, <2>5
<1>balsfin. IsFiniteSet(Bals)
  <2>1. IsFiniteSet(0..bd)  BY FS_Interval
  <2> QED BY <2>1, <1>balssub, FS_Subset
<1>balsne. Bals # {}  BY <1>ne
<1>balssubnat. Bals \subseteq Nat  BY <1>balssub
<1>maxex. \E r \in Bals : \A y \in Bals : y <= r
  BY <1>balsfin, <1>balsne, <1>balssubnat, NatMaxExists
<1> PICK hibal \in Bals : \A y \in Bals : y <= hibal  BY <1>maxex
<1> PICK x \in Cand : B(x) = hibal  OBVIOUS
<1>xTC. x \in TranClosure(mm) /\ beta \in Lrns(x)  OBVIOUS
<1>xmax. \A y \in TranClosure(mm) : beta \in Lrns(y) => B(y) <= B(x)
  <2> SUFFICES ASSUME NEW y \in TranClosure(mm), beta \in Lrns(y) PROVE B(y) <= B(x)  OBVIOUS
  <2>1. y \in Cand  OBVIOUS
  <2>2. B(y) \in Bals  BY <2>1
  <2> QED BY <2>2
<1> QED BY <1>xTC, <1>xmax DEF TopLearnerMsg

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

LEMMA CatchWitnessCorrect ==
  ASSUME TypeOKMessageInterface, NEW mm \in SUBSET Messages, NEW s,
         s \in CaughtS(TranClosure(mm))
  PROVE /\ CatchWitness1(mm,s) \in TranClosure(mm)
        /\ CatchWitness2(mm,s) \in TranClosure(mm)
        /\ Sig(CatchWitness1(mm,s)) = s /\ Sig(CatchWitness2(mm,s)) = s
        /\ CatchWitness1(mm,s) \notin Tran(CatchWitness2(mm,s))
        /\ CatchWitness2(mm,s) \notin Tran(CatchWitness1(mm,s))
<1>ex. \E x \in TranClosure(mm) : \E y \in TranClosure(mm) :
         /\ Sig(x) = s /\ Sig(y) = s
         /\ x \notin Tran(y) /\ y \notin Tran(x)
  BY DEF CaughtS
<1>c1props. /\ CatchWitness1(mm,s) \in TranClosure(mm)
            /\ \E y \in TranClosure(mm) :
                 /\ Sig(CatchWitness1(mm,s)) = s /\ Sig(y) = s
                 /\ CatchWitness1(mm,s) \notin Tran(y) /\ y \notin Tran(CatchWitness1(mm,s))
  BY <1>ex DEF CatchWitness1
<1>c2props. /\ CatchWitness2(mm,s) \in TranClosure(mm)
            /\ Sig(CatchWitness1(mm,s)) = s /\ Sig(CatchWitness2(mm,s)) = s
            /\ CatchWitness1(mm,s) \notin Tran(CatchWitness2(mm,s))
            /\ CatchWitness2(mm,s) \notin Tran(CatchWitness1(mm,s))
  BY <1>c1props DEF CatchWitness2
<1> QED BY <1>c1props, <1>c2props

\* --- the finite witness set C ---
\* Per-acceptor "chain top" witnesses are NOT needed: with AlwaysANewProposal
\* strengthened to guarantee Sig(p) \notin Acceptors, p can never be one of
\* the two same-signer messages CaughtS looks for, so p can never introduce a
\* NEW catch regardless of any uncaught acceptor's chain length/shape.  C
\* only needs (a) witness pairs for acceptors ALREADY caught in TranClosure(m)
\* (so oneb doesn't LOSE any existing catch) and (b) per-learner top-ballot
\* witnesses (for the Fresh clause-(c) chain argument).
CaughtAcc(mm) == CaughtS(TranClosure(mm))
RelevantLearners(mm) == {beta \in Learners : \E x \in TranClosure(mm) : beta \in Lrns(x)}

CQ(mm) ==
  {CatchWitness1(mm,s) : s \in CaughtAcc(mm)}
  \cup {CatchWitness2(mm,s) : s \in CaughtAcc(mm)}
  \cup {TopLearnerMsg(mm,beta) : beta \in RelevantLearners(mm)}

LEMMA CQFinite ==
  ASSUME LearnerGraphAssumptions, NEW mm \in SUBSET Messages
  PROVE IsFiniteSet(CQ(mm))
<1>acc. IsFiniteSet(Acceptors)  BY DEF LearnerGraphAssumptions, FiniteAcceptors
<1>lrn. IsFiniteSet(Learners)  BY DEF LearnerGraphAssumptions, FiniteLearners
<1>caughtsub. CaughtAcc(mm) \subseteq Acceptors  BY DEF CaughtAcc, CaughtS
<1>caughtfin. IsFiniteSet(CaughtAcc(mm))  BY <1>acc, <1>caughtsub, FS_Subset
<1>relsub. RelevantLearners(mm) \subseteq Learners  BY DEF RelevantLearners
<1>relfin. IsFiniteSet(RelevantLearners(mm))  BY <1>lrn, <1>relsub, FS_Subset
<1>p1. IsFiniteSet({CatchWitness1(mm,s) : s \in CaughtAcc(mm)})  BY <1>caughtfin, FS_Image
<1>p2. IsFiniteSet({CatchWitness2(mm,s) : s \in CaughtAcc(mm)})  BY <1>caughtfin, FS_Image
<1>p3. IsFiniteSet({TopLearnerMsg(mm,beta) : beta \in RelevantLearners(mm)})  BY <1>relfin, FS_Image
<1>u12. IsFiniteSet({CatchWitness1(mm,s) : s \in CaughtAcc(mm)}
                    \cup {CatchWitness2(mm,s) : s \in CaughtAcc(mm)})
  BY <1>p1, <1>p2, FS_Union
<1> QED BY <1>u12, <1>p3, FS_Union DEF CQ

LEMMA CQSubTC ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, AlwaysAProposal,
         NEW mm \in SUBSET Messages, NEW bd \in Nat,
         \A x \in TranClosure(mm) : B(x) < bd
  PROVE CQ(mm) \subseteq TranClosure(mm)
<1> SUFFICES ASSUME NEW z \in CQ(mm) PROVE z \in TranClosure(mm)  OBVIOUS
<1>1. \/ z \in {CatchWitness1(mm,s) : s \in CaughtAcc(mm)}
      \/ z \in {CatchWitness2(mm,s) : s \in CaughtAcc(mm)}
      \/ z \in {TopLearnerMsg(mm,beta) : beta \in RelevantLearners(mm)}
  BY DEF CQ
<1>a. CASE z \in {CatchWitness1(mm,s) : s \in CaughtAcc(mm)}
  <2> PICK s \in CaughtAcc(mm) : z = CatchWitness1(mm,s)  BY <1>a
  <2>cw. s \in CaughtS(TranClosure(mm))  BY DEF CaughtAcc
  <2> QED BY <2>cw, CatchWitnessCorrect
<1>b. CASE z \in {CatchWitness2(mm,s) : s \in CaughtAcc(mm)}
  <2> PICK s \in CaughtAcc(mm) : z = CatchWitness2(mm,s)  BY <1>b
  <2>cw. s \in CaughtS(TranClosure(mm))  BY DEF CaughtAcc
  <2> QED BY <2>cw, CatchWitnessCorrect
<1>d. CASE z \in {TopLearnerMsg(mm,beta) : beta \in RelevantLearners(mm)}
  <2> PICK beta \in RelevantLearners(mm) : z = TopLearnerMsg(mm,beta)  BY <1>d
  <2>ex. \E x \in TranClosure(mm) : beta \in Lrns(x)  BY DEF RelevantLearners
  <2> QED BY <2>ex, TopLearnerMsgCorrect
<1> QED BY <1>1, <1>a, <1>b, <1>d

\* --- constructing p ---
LEMMA PExists ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions, ValueInterfaceAssumptions,
         NEW m \in SUBSET Messages, NEW bal \in Ballots, NEW targetVal \in Values,
         \A x \in TranClosure(m) : B(x) < bal
  PROVE \E p \in Proposals :
          /\ TranExclusive(p) = TranClosure(CQ(m))
          /\ B(p) > bal
          /\ Sig(p) \notin Acceptors
          /\ V(p) = targetVal
<1>mi. TypeOKMessageInterface /\ TranTrans /\ TranFinite /\ AlwaysAProposal /\ AlwaysANewProposal
  BY DEF MessageInterfaceAssumptions
<1>lga. LearnerGraphAssumptions  OBVIOUS
<1>via. AlwaysAHigherBallot  BY DEF ValueInterfaceAssumptions
<1>cfin. IsFiniteSet(CQ(m))  BY <1>lga, CQFinite
<1>balnat. bal \in Nat  BY DEF Ballots
<1>bound. \A x \in TranClosure(m) : B(x) < bal  OBVIOUS
<1>csub. CQ(m) \subseteq TranClosure(m)  BY <1>mi, <1>balnat, <1>bound, CQSubTC
<1>hb. \E b \in Ballots : bal < b /\ BalToVal(b) = targetVal  BY <1>via DEF AlwaysAHigherBallot
<1> PICK b \in Ballots : bal < b /\ BalToVal(b) = targetVal  BY <1>hb
<1>bnat. b \in Nat  BY DEF Ballots
<1>cballs. \A x \in CQ(m) : B(x) < b
  <2> SUFFICES ASSUME NEW x \in CQ(m) PROVE B(x) < b  OBVIOUS
  <2>1. x \in TranClosure(m)  BY <1>csub
  <2>1m. x \in Messages  BY <2>1, <1>mi, TranClosureClosed
  <2>2. B(x) < bal  BY <2>1, <1>bound
  <2>3. B(x) \in Ballots  BY <2>1m, <1>mi, BBallot
  <2>4. B(x) \in Nat  BY <2>3 DEF Ballots
  <2> QED BY <2>2, <2>4, <1>balnat, <1>bnat
<1>cqmsgs. CQ(m) \in SUBSET Messages
  <2> SUFFICES ASSUME NEW z \in CQ(m) PROVE z \in Messages  OBVIOUS
  <2>1. z \in TranClosure(m)  BY <1>csub
  <2> QED BY <2>1, <1>mi, TranClosureClosed
<1>anp. \E p \in Proposals :
          /\ TranExclusive(p) = TranClosure(CQ(m))
          /\ B(p) = b
          /\ Sig(p) \notin Acceptors
  BY <1>mi, <1>cqmsgs, <1>cfin, <1>cballs DEF AlwaysANewProposal
<1> PICK p \in Proposals :
      /\ TranExclusive(p) = TranClosure(CQ(m))
      /\ B(p) = b
      /\ Sig(p) \notin Acceptors
  BY <1>anp
<1>vp. V(p) = targetVal  BY DEF V
<1> QED BY <1>vp

\* --- CaughtS bookkeeping when adding one message ---
LEMMA CaughtSAddNonAcceptor ==
  ASSUME TypeOKMessageInterface, NEW M \in SUBSET Messages, NEW q, Sig(q) \notin Acceptors
  PROVE CaughtS(M \cup {q}) = CaughtS(M)
<1>fwd. CaughtS(M) \subseteq CaughtS(M \cup {q})  BY DEF CaughtS
<1>bwd. CaughtS(M \cup {q}) \subseteq CaughtS(M)
  <2> SUFFICES ASSUME NEW s \in CaughtS(M \cup {q}) PROVE s \in CaughtS(M)  OBVIOUS
  <2>1. PICK m1 \in M \cup {q}, m2 \in M \cup {q} :
          /\ Sig(m1) = s /\ Sig(m2) = s
          /\ m1 \notin Tran(m2) /\ m2 \notin Tran(m1)
    BY DEF CaughtS
  <2>sacc. s \in Acceptors  BY <2>1 DEF CaughtS
  <2>2. m1 # q  BY <2>1, <2>sacc
  <2>3. m2 # q  BY <2>1, <2>sacc
  <2>4. m1 \in M /\ m2 \in M  BY <2>1, <2>2, <2>3
  <2> QED BY <2>1, <2>4, <2>sacc DEF CaughtS
<1> QED BY <1>fwd, <1>bwd

LEMMA CaughtSAddOne ==
  ASSUME TypeOKMessageInterface, NEW M \in SUBSET Messages, NEW q, NEW a \in Acceptors,
         Sig(q) = a, a \notin CaughtS(M \cup {q})
  PROVE CaughtS(M \cup {q}) = CaughtS(M)
<1>fwd. CaughtS(M) \subseteq CaughtS(M \cup {q})  BY DEF CaughtS
<1>bwd. CaughtS(M \cup {q}) \subseteq CaughtS(M)
  <2> SUFFICES ASSUME NEW s \in CaughtS(M \cup {q}) PROVE s \in CaughtS(M)  OBVIOUS
  <2>1. PICK m1 \in M \cup {q}, m2 \in M \cup {q} :
          /\ Sig(m1) = s /\ Sig(m2) = s
          /\ m1 \notin Tran(m2) /\ m2 \notin Tran(m1)
    BY DEF CaughtS
  <2>sacc. s \in Acceptors  BY <2>1 DEF CaughtS
  <2>sa. s # a  BY <2>1, <2>sacc DEF CaughtS
  <2>2. m1 # q  BY <2>1, <2>sa
  <2>3. m2 # q  BY <2>1, <2>sa
  <2>4. m1 \in M /\ m2 \in M  BY <2>1, <2>2, <2>3
  <2> QED BY <2>1, <2>4, <2>sacc DEF CaughtS
<1> QED BY <1>fwd, <1>bwd

\* --- basic TranClosure algebra ---
LEMMA TranClosureUnion ==
  ASSUME NEW A, NEW B
  PROVE TranClosure(A \cup B) = TranClosure(A) \cup TranClosure(B)
BY DEF TranClosure

LEMMA TranClosureSingleton == ASSUME NEW q PROVE TranClosure({q}) = Tran(q)
BY DEF TranClosure

LEMMA TranClosureAbsorb ==
  ASSUME TypeOKMessageInterface, TranTrans, NEW mm \in SUBSET Messages, NEW Msgs \in SUBSET Messages,
         Msgs \subseteq TranClosure(mm)
  PROVE TranClosure(Msgs) \subseteq TranClosure(mm)
<1> SUFFICES ASSUME NEW z \in TranClosure(Msgs) PROVE z \in TranClosure(mm)  OBVIOUS
<1>1. PICK x \in Msgs : z \in Tran(x)  BY DEF TranClosure
<1>2. x \in TranClosure(mm)  BY <1>1
<1>3. Tran(x) \subseteq TranClosure(mm)  BY <1>2, TranClosureClosed
<1> QED BY <1>1, <1>3

LEMMA TranClosureExpanding == ASSUME NEW S PROVE S \subseteq TranClosure(S)
<1> SUFFICES ASSUME NEW x \in S PROVE x \in TranClosure(S)  OBVIOUS
<1>1. x \in Tran(x)  BY DEF Tran
<1> QED BY <1>1 DEF TranClosure

LEMMA TranClosureIdempotent ==
  ASSUME TypeOKMessageInterface, TranTrans, NEW mm \in SUBSET Messages
  PROVE TranClosure(TranClosure(mm)) = TranClosure(mm)
<1>tcmsgs. TranClosure(mm) \in SUBSET Messages
  <2> SUFFICES ASSUME NEW z \in TranClosure(mm) PROVE z \in Messages  OBVIOUS
  <2> QED BY TranClosureClosed
<1>sub. TranClosure(TranClosure(mm)) \subseteq TranClosure(mm)
  <2>1. TranClosure(mm) \subseteq TranClosure(mm)  OBVIOUS
  <2> QED BY <2>1, <1>tcmsgs, TranClosureAbsorb
<1>sup. TranClosure(mm) \subseteq TranClosure(TranClosure(mm))  BY TranClosureExpanding
<1> QED BY <1>sub, <1>sup

\* --- B / ProposalBal bookkeeping ---
LEMMA ProposalBalLeB ==
  ASSUME MessageInterfaceAssumptions, NEW y, y \in Proposals
  PROVE ProposalBal(y) <= B(y)
<1>tok. TypeOKMessageInterface  BY DEF MessageInterfaceAssumptions
<1>tf. TranFinite  BY DEF MessageInterfaceAssumptions
<1>propsub. Proposals \subseteq Messages  BY <1>tok DEF TypeOKMessageInterface
<1>ym. y \in Messages  BY <1>propsub
<1>ygp. y \in GetProposals(y)
  <2>1. y \in Tran(y)  BY DEF Tran
  <2> QED BY <2>1 DEF GetProposals
<1>fin. IsFiniteSet(GetProposals(y))
  <2>1. GetProposals(y) \subseteq Tran(y)  BY DEF GetProposals
  <2>2. IsFiniteSet(Tran(y))  BY <1>ym, <1>tf DEF TranFinite
  <2> QED BY <2>1, <2>2, FS_Subset
<1>ne. GetProposals(y) # {}  BY <1>ygp
<1>sub. GetProposals(y) \subseteq Proposals  BY DEF GetProposals
<1>choose. /\ B(y) \in {ProposalBal(z) : z \in GetProposals(y)}
           /\ \A w \in {ProposalBal(z) : z \in GetProposals(y)} : B(y) >= w
  BY <1>tok, <1>fin, <1>sub, <1>ne, MaxBSetProperty DEF B
<1> QED BY <1>choose, <1>ygp

\* Any message's B-value is achieved by some ancestor proposal (in its own
\* Tran) whose own B-value equals it too.
LEMMA BAchievedByProposal ==
  ASSUME MessageInterfaceAssumptions, NEW w \in Messages
  PROVE \E q \in Tran(w) : IsProposal(q) /\ ProposalBal(q) = B(w) /\ B(q) = B(w)
<1>tok. TypeOKMessageInterface  BY DEF MessageInterfaceAssumptions
<1>tf. TranFinite  BY DEF MessageInterfaceAssumptions
<1>tt. TranTrans  BY DEF MessageInterfaceAssumptions
<1>anp. AlwaysAProposal  BY DEF MessageInterfaceAssumptions
<1>ne. GetProposals(w) # {}  BY <1>anp DEF AlwaysAProposal
<1>sub. GetProposals(w) \subseteq Proposals  BY DEF GetProposals
<1>fin. IsFiniteSet(GetProposals(w))
  <2>1. GetProposals(w) \subseteq Tran(w)  BY DEF GetProposals
  <2>2. IsFiniteSet(Tran(w))  BY <1>tf DEF TranFinite
  <2> QED BY <2>1, <2>2, FS_Subset
<1>choose. /\ B(w) \in {ProposalBal(z) : z \in GetProposals(w)}
           /\ \A y \in {ProposalBal(z) : z \in GetProposals(w)} : B(w) >= y
  BY <1>tok, <1>fin, <1>sub, <1>ne, MaxBSetProperty DEF B
<1> PICK q \in GetProposals(w) : B(w) = ProposalBal(q)  BY <1>choose
<1>qgp. q \in Proposals /\ q \in Tran(w)  BY DEF GetProposals
<1>qprop. IsProposal(q)  BY <1>qgp DEF IsProposal
<1>propsub. Proposals \subseteq Messages  BY <1>tok DEF TypeOKMessageInterface
<1>qmsg. q \in Messages  BY <1>qgp, <1>propsub
<1>qown. q \in GetProposals(q)
  <2>1. q \in Tran(q)  BY DEF Tran
  <2> QED BY <2>1, <1>qgp DEF GetProposals
<1>qfin. IsFiniteSet(GetProposals(q))
  <2>1. GetProposals(q) \subseteq Tran(q)  BY DEF GetProposals
  <2>2. IsFiniteSet(Tran(q))  BY <1>qmsg, <1>tf DEF TranFinite
  <2> QED BY <2>1, <2>2, FS_Subset
<1>qsub. GetProposals(q) \subseteq Proposals  BY DEF GetProposals
<1>qne. GetProposals(q) # {}  BY <1>qown
<1>choose2. /\ B(q) \in {ProposalBal(z) : z \in GetProposals(q)}
            /\ \A y \in {ProposalBal(z) : z \in GetProposals(q)} : B(q) >= y
  BY <1>tok, <1>qfin, <1>qsub, <1>qne, MaxBSetProperty DEF B
<1>bqge. B(q) >= ProposalBal(q)
  <2>pbmem. ProposalBal(q) \in {ProposalBal(z) : z \in GetProposals(q)}  BY <1>qown
  <2> QED BY <2>pbmem, <1>choose2
<1>gpsub. GetProposals(q) \subseteq GetProposals(w)
  <2>1. Tran(q) \subseteq Tran(w)  BY <1>qgp, <1>tt DEF TranTrans
  <2> QED BY <2>1 DEF GetProposals
<1>bqmem. B(q) \in {ProposalBal(z) : z \in GetProposals(w)}
  <2>1. B(q) \in {ProposalBal(z) : z \in GetProposals(q)}  BY <1>choose2
  <2> QED BY <2>1, <1>gpsub
<1>bqle. B(w) >= B(q)  BY <1>bqmem, <1>choose
<1>anp2. AlwaysAProposal  BY <1>anp
<1>bwnat. B(w) \in Ballots  BY <1>tok, <1>tf, <1>anp2, BBallot
<1>bqnat. B(q) \in Ballots  BY <1>qmsg, <1>tok, <1>tf, <1>anp2, BBallot
<1>beq. B(q) = B(w)  BY <1>bqge, <1>bqle, <1>bwnat, <1>bqnat DEF Ballots
<1> QED BY <1>qgp, <1>qprop, <1>beq

LEMMA ProposalBalOfP ==
  ASSUME MessageInterfaceAssumptions, NEW mm \in SUBSET Messages, NEW p, NEW b \in Ballots,
         p \in Proposals, TranExclusive(p) = TranClosure(mm), B(p) = b,
         \A x \in TranClosure(mm) : B(x) < b
  PROVE ProposalBal(p) = b
<1>tok. TypeOKMessageInterface  BY DEF MessageInterfaceAssumptions
<1>tf. TranFinite  BY DEF MessageInterfaceAssumptions
<1>anp. AlwaysAProposal  BY DEF MessageInterfaceAssumptions
<1>propsub. Proposals \subseteq Messages  BY <1>tok DEF TypeOKMessageInterface
<1>pm. p \in Messages  BY <1>propsub
<1>pgp. p \in GetProposals(p)
  <2>1. p \in Tran(p)  BY DEF Tran
  <2> QED BY <2>1 DEF GetProposals
<1>fin. IsFiniteSet(GetProposals(p))
  <2>1. GetProposals(p) \subseteq Tran(p)  BY DEF GetProposals
  <2>2. IsFiniteSet(Tran(p))  BY <1>pm, <1>tf DEF TranFinite
  <2> QED BY <2>1, <2>2, FS_Subset
<1>ne. GetProposals(p) # {}  BY <1>pgp
<1>sub. GetProposals(p) \subseteq Proposals  BY DEF GetProposals
<1>choose. /\ B(p) \in {ProposalBal(z) : z \in GetProposals(p)}
           /\ \A w \in {ProposalBal(z) : z \in GetProposals(p)} : B(p) >= w
  BY <1>tok, <1>fin, <1>sub, <1>ne, MaxBSetProperty DEF B
<1> PICK z \in GetProposals(p) : B(p) = ProposalBal(z)  BY <1>choose
<1>zgp. z \in Proposals /\ z \in Tran(p)  BY DEF GetProposals
<1>zcase. z = p \/ z \in TranExclusive(p)  BY <1>zgp DEF TranExclusive
<1>notother. z \in TranExclusive(p) => FALSE
  <2> SUFFICES ASSUME z \in TranExclusive(p) PROVE FALSE  OBVIOUS
  <2>1. z \in TranClosure(mm)  OBVIOUS
  <2>2. B(z) < b  BY <2>1
  <2>3. ProposalBal(z) <= B(z)  BY <1>zgp, ProposalBalLeB
  <2>4. ProposalBal(z) = B(p)  BY <1>choose
  <2>5. B(p) = b  OBVIOUS
  <2>zmsg. z \in Messages  BY <1>zgp, <1>propsub
  <2>pbz. ProposalBal(z) \in Ballots  BY <1>zgp, <1>tok DEF TypeOKMessageInterface
  <2>bz. B(z) \in Ballots  BY <2>zmsg, <1>tok, <1>tf, <1>anp, BBallot
  <2>bp. B(p) \in Ballots  BY <1>pm, <1>tok, <1>tf, <1>anp, BBallot
  <2> QED BY <2>2, <2>3, <2>4, <2>5, <2>pbz, <2>bz, <2>bp DEF Ballots
<1>zisp. z = p  BY <1>zcase, <1>notother
<1> QED BY <1>choose, <1>zisp

\* B of a non-proposal y whose exclusive ancestry S contains a proposal p at
\* the max ballot b (everything else in S strictly below b).
LEMMA BOfAbsorbing ==
  ASSUME MessageInterfaceAssumptions,
         NEW y \in Messages, NEW S \in SUBSET Messages, NEW p, NEW b \in Ballots,
         TranExclusive(y) = S, y \notin Proposals,
         p \in S, p \in Proposals, ProposalBal(p) = b,
         \A x \in S : x # p => B(x) < b
  PROVE B(y) = b
<1>tok. TypeOKMessageInterface  BY DEF MessageInterfaceAssumptions
<1>tf. TranFinite  BY DEF MessageInterfaceAssumptions
<1>anp. AlwaysAProposal  BY DEF MessageInterfaceAssumptions
<1>pty. p \in Tran(y)  BY DEF TranExclusive
<1>pgp. p \in GetProposals(y)  BY <1>pty DEF GetProposals
<1>fin. IsFiniteSet(GetProposals(y))
  <2>1. GetProposals(y) \subseteq Tran(y)  BY DEF GetProposals
  <2>2. IsFiniteSet(Tran(y))  BY <1>tf DEF TranFinite
  <2> QED BY <2>1, <2>2, FS_Subset
<1>ne. GetProposals(y) # {}  BY <1>pgp
<1>sub. GetProposals(y) \subseteq Proposals  BY DEF GetProposals
<1>choose. /\ B(y) \in {ProposalBal(z) : z \in GetProposals(y)}
           /\ \A w \in {ProposalBal(z) : z \in GetProposals(y)} : B(y) >= w
  BY <1>tok, <1>fin, <1>sub, <1>ne, MaxBSetProperty DEF B
<1>ge. B(y) >= b  BY <1>choose, <1>pgp
<1> PICK z \in GetProposals(y) : B(y) = ProposalBal(z)  BY <1>choose
<1>zgp. z \in Proposals /\ z \in Tran(y)  BY DEF GetProposals
<1>zisynotprop. z # y  BY <1>zgp
<1>zte. z \in TranExclusive(y)  BY <1>zgp, <1>zisynotprop DEF TranExclusive
<1>zinS. z \in S  BY <1>zte
<1>zbalp. B(y) = ProposalBal(z)  OBVIOUS
<1>zisp. z = p
  <2> SUFFICES ASSUME z # p PROVE FALSE  OBVIOUS
  <2>1. B(z) < b  BY <1>zinS
  <2>2. ProposalBal(z) <= B(z)  BY <1>zgp, ProposalBalLeB
  <2>zprop. z \in Proposals  BY <1>zgp
  <2>zmsg. z \in Messages  BY <2>zprop, <1>tok DEF TypeOKMessageInterface
  <2>pbz. ProposalBal(z) \in Ballots  BY <2>zprop, <1>tok DEF TypeOKMessageInterface, ProposalBal
  <2>bz. B(z) \in Ballots  BY <2>zmsg, <1>tok, <1>tf, <1>anp, BBallot
  <2>bnat. b \in Nat  BY DEF Ballots
  <2>3. B(y) < b  BY <2>1, <2>2, <1>zbalp, <2>pbz, <2>bz, <2>bnat DEF Ballots
  <2>ybal. B(y) \in Ballots  BY <1>tok, <1>tf, <1>anp, BBallot
  <2> QED BY <2>3, <1>ge, <2>bnat, <2>ybal DEF Ballots
<1> QED BY <1>zisp

\* --- constructing oneb ---
\* Wrapper with fresh bound-var names (mm/bb/aa) to avoid the AlwaysANewOneB
\* axiom's own internal m/b/a binders colliding with a caller's identically-named
\* ambient m/a (the same shadowing class as TranClosureAbsorb's old S param).
\* bb is bundled into an \E premise (rather than left as a plain NEW) since it
\* does not appear in the conclusion -- a "hidden" lemma parameter that a
\* backend must otherwise blind-search a witness for during application.
LEMMA AlwaysANewOneBInst ==
  ASSUME MessageInterfaceAssumptions,
         NEW mm \in SUBSET Messages, NEW aa \in Acceptors,
         \E bb \in Ballots :
           /\ IsFiniteSet(mm)
           /\ (\A x \in mm : B(x) <= bb)
           /\ Cardinality({x \in TranClosure(mm) : B(x) = bb}) = 1
           /\ aa \notin CaughtS(TranClosure(mm))
  PROVE \E x \in Messages :
          /\ Sig(x) = aa
          /\ aa \notin Caught(x)
          /\ IsOneB(x)
          /\ TranExclusive(x) = TranClosure(mm)
<1> PICK bb \in Ballots :
      /\ IsFiniteSet(mm)
      /\ (\A x \in mm : B(x) <= bb)
      /\ Cardinality({x \in TranClosure(mm) : B(x) = bb}) = 1
      /\ aa \notin CaughtS(TranClosure(mm))
  OBVIOUS
<1>anob. AlwaysANewOneB  BY DEF MessageInterfaceAssumptions
<1> QED BY <1>anob DEF AlwaysANewOneB

LEMMA OneBExists ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions,
         NEW m \in SUBSET Messages, NEW bal \in Ballots,
         NEW p, NEW btarg \in Ballots,
         p \in Proposals, TranExclusive(p) = TranClosure(CQ(m)), B(p) = btarg, Sig(p) \notin Acceptors,
         \A x \in TranClosure(m) : B(x) < bal,
         bal < btarg,
         NEW a \in Acceptors, NEW known \in SUBSET TranClosure(m), IsFiniteSet(known),
         a \notin CaughtS(TranClosure(known \cup TranExclusive(p)))
  PROVE \E oneb \in Messages :
          /\ Sig(oneb) = a
          /\ a \notin Caught(oneb)
          /\ IsOneB(oneb)
          /\ TranExclusive(oneb) = TranClosure(known \cup {p})
          /\ B(oneb) = btarg
          /\ Caught(oneb) = CaughtS(TranClosure(m))
<1>mi. TypeOKMessageInterface /\ TranTrans /\ TranFinite /\ AlwaysAProposal /\ AlwaysANewOneB
  BY DEF MessageInterfaceAssumptions
<1>anob. AlwaysANewOneB  BY DEF MessageInterfaceAssumptions
<1>cfin. IsFiniteSet(CQ(m))  BY LearnerGraphAssumptions, CQFinite
<1>balnat. bal \in Nat  BY DEF Ballots
<1>btnat. btarg \in Nat  BY DEF Ballots
<1>bound. \A x \in TranClosure(m) : B(x) < bal  OBVIOUS
<1>csub. CQ(m) \subseteq TranClosure(m)  BY <1>mi, <1>balnat, <1>bound, CQSubTC
<1>tepeq. TranExclusive(p) = TranClosure(CQ(m))  OBVIOUS
<1>cqmsgs. CQ(m) \in SUBSET Messages
  <2> SUFFICES ASSUME NEW z \in CQ(m) PROVE z \in Messages  OBVIOUS
  <2>1. z \in TranClosure(m)  BY <1>csub
  <2> QED BY <2>1, <1>mi, TranClosureClosed
<1>tepsub. TranExclusive(p) \subseteq TranClosure(m)  BY <1>tepeq, <1>csub, <1>cqmsgs, <1>mi, TranClosureAbsorb
<1>tepidem. TranClosure(TranExclusive(p)) = TranExclusive(p)
  BY <1>tepeq, <1>cqmsgs, <1>mi, TranClosureIdempotent
<1>knownmsgs. known \in SUBSET Messages
  <2> SUFFICES ASSUME NEW z \in known PROVE z \in Messages  OBVIOUS
  <2>1. z \in TranClosure(m)  OBVIOUS
  <2> QED BY <2>1, <1>mi, TranClosureClosed
<1>knownsub. TranClosure(known) \subseteq TranClosure(m)  BY <1>mi, <1>knownmsgs, TranClosureAbsorb
<1>tc1. TranClosure(known \cup TranExclusive(p)) = TranClosure(known) \cup TranExclusive(p)
  <2>1. TranClosure(known \cup TranExclusive(p)) = TranClosure(known) \cup TranClosure(TranExclusive(p))
    BY TranClosureUnion
  <2> QED BY <2>1, <1>tepidem
<1>tc2. TranClosure(known \cup {p}) = TranClosure(known) \cup Tran(p)
  <2>1. TranClosure(known \cup {p}) = TranClosure(known) \cup TranClosure({p})  BY TranClosureUnion
  <2>2. TranClosure({p}) = Tran(p)  BY TranClosureSingleton
  <2> QED BY <2>1, <2>2
<1>tranp. Tran(p) = {p} \cup TranExclusive(p)  BY DEF Tran, TranExclusive
<1>tc3. TranClosure(known \cup {p}) = TranClosure(known \cup TranExclusive(p)) \cup {p}
  BY <1>tc1, <1>tc2, <1>tranp
<1>oldballs. \A x \in TranClosure(known \cup TranExclusive(p)) : B(x) < bal
  BY <1>tc1, <1>knownsub, <1>tepsub
<1>ktepmsgs. TranClosure(known \cup TranExclusive(p)) \subseteq Messages
  <2> SUFFICES ASSUME NEW z \in TranClosure(known \cup TranExclusive(p)) PROVE z \in Messages  OBVIOUS
  <2>1. z \in TranClosure(m)  BY <1>tc1, <1>knownsub, <1>tepsub
  <2> QED BY <2>1, <1>mi, TranClosureClosed
<1>knownfin. IsFiniteSet(known \cup {p})  BY FS_Singleton, FS_Union
<1>bpbtarg. B(p) = btarg  OBVIOUS
<1>baltbarg2. bal < btarg  OBVIOUS
<1>ballsleb. \A x \in known \cup {p} : B(x) <= btarg
  <2> SUFFICES ASSUME NEW x \in known \cup {p} PROVE B(x) <= btarg  OBVIOUS
  <2>1. CASE x = p
    <3>bxp. B(x) = B(p)  BY <2>1
    <3> QED BY <3>bxp, <1>bpbtarg, <1>btnat
  <2>2. CASE x \in known
    <3>1. x \in TranClosure(m)  BY <2>2
    <3>2. B(x) < bal  BY <3>1, <1>bound
    <3>3. B(x) \in Ballots  BY <3>1, <1>mi, TranClosureClosed, BBallot
    <3> QED BY <3>2, <3>3, <1>baltbarg2, <1>balnat, <1>btnat DEF Ballots
  <2> QED BY <2>1, <2>2
<1>cardone. Cardinality({x \in TranClosure(known \cup {p}) : B(x) = btarg}) = 1
  <2>eq. {x \in TranClosure(known \cup {p}) : B(x) = btarg} = {p}
    <3> SUFFICES ASSUME NEW x \in TranClosure(known \cup {p}), B(x) = btarg
                 PROVE x = p
      BY <1>tc3
    <3>1. x \in TranClosure(known \cup TranExclusive(p)) \/ x = p  BY <1>tc3
    <3>2. CASE x = p  BY <3>2
    <3>3. CASE x \in TranClosure(known \cup TranExclusive(p))
      <4>1. B(x) < bal  BY <3>3, <1>oldballs
      <4>2. x \in Messages  BY <3>3, <1>ktepmsgs
      <4>3. B(x) \in Ballots  BY <4>2, <1>mi, BBallot
      <4> QED BY <4>1, <4>3, <1>baltbarg2, <1>balnat, <1>btnat DEF Ballots
    <3> QED BY <3>1, <3>2, <3>3
  <2> QED BY <2>eq, FS_Singleton
<1>capp. a \notin CaughtS(TranClosure(known \cup {p}))
  <2>1. CaughtS(TranClosure(known \cup {p})) = CaughtS(TranClosure(known \cup TranExclusive(p)) \cup {p})
    BY <1>tc3
  <2>2. CaughtS(TranClosure(known \cup TranExclusive(p)) \cup {p})
          = CaughtS(TranClosure(known \cup TranExclusive(p)))
    BY <1>mi, <1>ktepmsgs, CaughtSAddNonAcceptor
  <2> QED BY <2>1, <2>2
<1>anexhyp. \E bb \in Ballots :
             /\ IsFiniteSet(known \cup {p})
             /\ (\A x \in known \cup {p} : B(x) <= bb)
             /\ Cardinality({x \in TranClosure(known \cup {p}) : B(x) = bb}) = 1
             /\ a \notin CaughtS(TranClosure(known \cup {p}))
  <2> WITNESS btarg \in Ballots
  <2> QED BY <1>knownfin, <1>ballsleb, <1>cardone, <1>capp, <1>btnat
<1>anb. \E oneb \in Messages :
          /\ Sig(oneb) = a
          /\ a \notin Caught(oneb)
          /\ IsOneB(oneb)
          /\ TranExclusive(oneb) = TranClosure(known \cup {p})
  <2> PICK bb \in Ballots :
        /\ IsFiniteSet(known \cup {p})
        /\ (\A x \in known \cup {p} : B(x) <= bb)
        /\ Cardinality({x \in TranClosure(known \cup {p}) : B(x) = bb}) = 1
        /\ a \notin CaughtS(TranClosure(known \cup {p}))
    BY <1>anexhyp
  <2>kpm. known \cup {p} \in SUBSET Messages
    <3> SUFFICES ASSUME NEW z \in known \cup {p} PROVE z \in Messages  OBVIOUS
    <3>1. CASE z \in known  BY <3>1, <1>knownmsgs
    <3>2. CASE z = p  BY <3>2, <1>mi DEF TypeOKMessageInterface
    <3> QED BY <3>1, <3>2
  <2> PICK KP \in SUBSET Messages :
        /\ KP = known \cup {p}
        /\ IsFiniteSet(KP)
        /\ (\A x \in KP : B(x) <= bb)
        /\ Cardinality({x \in TranClosure(KP) : B(x) = bb}) = 1
        /\ a \notin CaughtS(TranClosure(KP))
    <3> WITNESS known \cup {p} \in SUBSET Messages
    <3> QED BY <2>kpm
  <2>ax. \E oneb \in Messages :
           /\ Sig(oneb) = a
           /\ a \notin Caught(oneb)
           /\ IsOneB(oneb)
           /\ TranExclusive(oneb) = TranClosure(KP)
    BY <1>anob DEF AlwaysANewOneB
  <2> QED BY <2>ax
<1> PICK oneb \in Messages :
      /\ Sig(oneb) = a
      /\ a \notin Caught(oneb)
      /\ IsOneB(oneb)
      /\ TranExclusive(oneb) = TranClosure(known \cup {p})
  BY <1>anb
<1>onebnotprop. oneb \notin Proposals  BY DEF IsOneB, IsProposal
<1>cqoldballs. \A x \in TranClosure(CQ(m)) : B(x) < btarg
  <2> SUFFICES ASSUME NEW x \in TranClosure(CQ(m)) PROVE B(x) < btarg  OBVIOUS
  <2>1. x \in TranClosure(m)  BY <1>csub, <1>mi, <1>cqmsgs, TranClosureAbsorb
  <2>2. B(x) < bal  BY <2>1, <1>bound
  <2>3. B(x) \in Ballots  BY <2>1, <1>mi, TranClosureClosed, BBallot
  <2> QED BY <2>2, <2>3, <1>baltbarg2, <1>balnat, <1>btnat DEF Ballots
<1>pbalp. ProposalBal(p) = btarg
  BY <1>tepeq, <1>cqmsgs, <1>bpbtarg, <1>cqoldballs, ProposalBalOfP
<1>notpballs. \A x \in TranClosure(known \cup {p}) : x # p => B(x) < btarg
  <2> SUFFICES ASSUME NEW x \in TranClosure(known \cup {p}), x # p PROVE B(x) < btarg  OBVIOUS
  <2>1. x \in TranClosure(known \cup TranExclusive(p))  BY <1>tc3
  <2>2. B(x) < bal  BY <2>1, <1>oldballs
  <2>3. x \in Messages  BY <2>1, <1>ktepmsgs
  <2>4. B(x) \in Ballots  BY <2>3, <1>mi, BBallot
  <2> QED BY <2>2, <2>4, <1>baltbarg2, <1>balnat, <1>btnat DEF Ballots
<1>pinS. p \in TranClosure(known \cup {p})
  <2>1. p \in Tran(p)  BY DEF Tran
  <2> QED BY <2>1 DEF TranClosure
<1>pmsg. p \in Messages  BY <1>mi DEF TypeOKMessageInterface
<1>kpmsgs. TranClosure(known \cup {p}) \subseteq Messages  BY <1>tc3, <1>ktepmsgs, <1>pmsg
<1>onebmsg. oneb \in Messages  OBVIOUS
<1>Boneb. B(oneb) = btarg
  BY <1>mi, <1>onebmsg, <1>kpmsgs, BOfAbsorbing, <1>onebnotprop, <1>pbalp, <1>notpballs, <1>pinS
<1>caughtoneb. Caught(oneb) = CaughtS(TranClosure(m))
  <2>ctran. Tran(oneb) = {oneb} \cup TranClosure(known \cup {p})  BY DEF TranExclusive, Tran
  <2>step1. CaughtS(TranClosure(known \cup TranExclusive(p))) = CaughtS(TranClosure(m))
    <3>sub1. TranClosure(known \cup TranExclusive(p)) \subseteq TranClosure(m)
      BY <1>tc1, <1>knownsub, <1>tepsub
    <3>fwd. CaughtS(TranClosure(known \cup TranExclusive(p))) \subseteq CaughtS(TranClosure(m))
      BY <3>sub1 DEF CaughtS
    <3>bwd. CaughtS(TranClosure(m)) \subseteq CaughtS(TranClosure(known \cup TranExclusive(p)))
      <4> SUFFICES ASSUME NEW s \in CaughtS(TranClosure(m))
                   PROVE s \in CaughtS(TranClosure(known \cup TranExclusive(p)))
        OBVIOUS
      <4>w1. s \in CaughtAcc(m)  BY DEF CaughtAcc
      <4>w2. CatchWitness1(m,s) \in CQ(m) /\ CatchWitness2(m,s) \in CQ(m)  BY <4>w1 DEF CQ
      <4>w3. CatchWitness1(m,s) \in TranClosure(CQ(m)) /\ CatchWitness2(m,s) \in TranClosure(CQ(m))
        BY <4>w2, TranClosureExpanding
      <4>w4. CatchWitness1(m,s) \in TranExclusive(p) /\ CatchWitness2(m,s) \in TranExclusive(p)
        BY <4>w3, <1>tepeq
      <4>w5. /\ Sig(CatchWitness1(m,s)) = s /\ Sig(CatchWitness2(m,s)) = s
             /\ CatchWitness1(m,s) \notin Tran(CatchWitness2(m,s))
             /\ CatchWitness2(m,s) \notin Tran(CatchWitness1(m,s))
        BY <1>mi, <4>w1, CatchWitnessCorrect DEF CaughtAcc
      <4>w6. CatchWitness1(m,s) \in TranClosure(known \cup TranExclusive(p))
             /\ CatchWitness2(m,s) \in TranClosure(known \cup TranExclusive(p))
        BY <4>w4, TranClosureExpanding
      <4> QED BY <4>w5, <4>w6 DEF CaughtS
    <3> QED BY <3>fwd, <3>bwd
  <2>step2. CaughtS(TranClosure(known \cup {p})) = CaughtS(TranClosure(known \cup TranExclusive(p)))
    <3>1. CaughtS(TranClosure(known \cup {p})) = CaughtS(TranClosure(known \cup TranExclusive(p)) \cup {p})
      BY <1>tc3
    <3>2. CaughtS(TranClosure(known \cup TranExclusive(p)) \cup {p})
            = CaughtS(TranClosure(known \cup TranExclusive(p)))
      BY <1>mi, <1>ktepmsgs, CaughtSAddNonAcceptor
    <3> QED BY <3>1, <3>2
  <2>step3. CaughtS({oneb} \cup TranClosure(known \cup {p})) = CaughtS(TranClosure(known \cup {p}))
    <3>comm. {oneb} \cup TranClosure(known \cup {p}) = TranClosure(known \cup {p}) \cup {oneb}  OBVIOUS
    <3>anot. a \notin CaughtS(TranClosure(known \cup {p}))  BY <1>capp
    <3>anotoneb. a \notin CaughtS(TranClosure(known \cup {p}) \cup {oneb})
      <4>1. CaughtS(TranClosure(known \cup {p}) \cup {oneb}) = Caught(oneb)  BY <3>comm, <2>ctran DEF Caught
      <4> QED BY <4>1
    <3>eq. CaughtS(TranClosure(known \cup {p}) \cup {oneb}) = CaughtS(TranClosure(known \cup {p}))
      BY <1>mi, <1>kpmsgs, <3>anot, <3>anotoneb, CaughtSAddOne
    <3> QED BY <3>comm, <3>eq
  <2> QED BY <2>ctran, <2>step1, <2>step2, <2>step3 DEF Caught
<1> QED BY <1>Boneb, <1>caughtoneb

\* --- picking beta*: the globally top-ballot per-learner witness ---
BXBeta(mm, beta) == B(TopLearnerMsg(mm, beta))

LEMMA BetaStarExists ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions,
         NEW mm \in SUBSET Messages, NEW SS \in SUBSET Learners, SS # {},
         \A beta \in SS : \E x \in TranClosure(mm) : beta \in Lrns(x),
         NEW bd \in Nat, \A x \in TranClosure(mm) : B(x) < bd
  PROVE \E beta \in SS : \A gamma \in SS : BXBeta(mm,gamma) <= BXBeta(mm,beta)
<1>mi. TypeOKMessageInterface /\ TranTrans /\ TranFinite /\ AlwaysAProposal  BY DEF MessageInterfaceAssumptions
<1>fin. IsFiniteSet(SS)
  <2>1. IsFiniteSet(Learners)  BY DEF LearnerGraphAssumptions, FiniteLearners
  <2> QED BY <2>1, FS_Subset
<1>nat. \A beta \in SS : BXBeta(mm,beta) \in Nat
  <2> SUFFICES ASSUME NEW beta \in SS PROVE BXBeta(mm,beta) \in Nat  OBVIOUS
  <2>1. TopLearnerMsg(mm,beta) \in TranClosure(mm)  BY <1>mi, TopLearnerMsgCorrect
  <2>2. TopLearnerMsg(mm,beta) \in Messages  BY <2>1, <1>mi, TranClosureClosed
  <2>3. B(TopLearnerMsg(mm,beta)) \in Ballots  BY <2>2, <1>mi, BBallot
  <2> QED BY <2>3 DEF Ballots, BXBeta
<1> QED BY <1>fin, SS # {}, <1>nat, FiniteMaxExists

\* --- Fresh(alpha, oneb) ---
LEMMA FreshOneb ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions,
         NEW m \in SUBSET Messages, NEW alpha \in Learners, NEW bal \in Ballots,
         NEW p, NEW btarg \in Ballots, NEW a \in Acceptors, NEW known \in SUBSET TranClosure(m),
         NEW oneb, NEW betastar \in Learners,
         p \in Proposals, TranExclusive(p) = TranClosure(CQ(m)), B(p) = btarg, Sig(p) \notin Acceptors,
         \A x \in TranClosure(m) : B(x) < bal, bal < btarg,
         oneb \in Messages, Sig(oneb) = a, IsOneB(oneb),
         TranExclusive(oneb) = TranClosure(known \cup {p}),
         B(oneb) = btarg,
         Caught(oneb) = CaughtS(TranClosure(m)),
         betastar \in ConFromCaught(alpha, CaughtS(TranClosure(m))),
         TopLearnerMsg(m,betastar) \in TranClosure(m),
         betastar \in Lrns(TopLearnerMsg(m,betastar)),
         \A beta \in ConFromCaught(alpha, CaughtS(TranClosure(m))) :
           (\E x \in TranClosure(m) : beta \in Lrns(x)) =>
           BXBeta(m,beta) <= BXBeta(m,betastar),
         V(p) = V(TopLearnerMsg(m,betastar))
  PROVE Fresh(alpha, oneb)
<1>mi. TypeOKMessageInterface /\ TranTrans /\ TranFinite /\ AlwaysAProposal  BY DEF MessageInterfaceAssumptions
<1>balnat. bal \in Nat  BY DEF Ballots
<1>bound. \A x \in TranClosure(m) : B(x) < bal  OBVIOUS
<1>bsmax. \A beta \in ConFromCaught(alpha, CaughtS(TranClosure(m))) :
            (\E x \in TranClosure(m) : beta \in Lrns(x)) => BXBeta(m,beta) <= BXBeta(m,betastar)
  OBVIOUS
<1>csub. CQ(m) \subseteq TranClosure(m)  BY <1>mi, <1>balnat, <1>bound, CQSubTC
<1>tepeq. TranExclusive(p) = TranClosure(CQ(m))  OBVIOUS
<1>cqmsgs. CQ(m) \in SUBSET Messages
  <2> SUFFICES ASSUME NEW z \in CQ(m) PROVE z \in Messages  OBVIOUS
  <2>1. z \in TranClosure(m)  BY <1>csub
  <2> QED BY <2>1, <1>mi, TranClosureClosed
<1>tepsub. TranExclusive(p) \subseteq TranClosure(m)  BY <1>tepeq, <1>csub, <1>cqmsgs, <1>mi, TranClosureAbsorb
<1>tepidem. TranClosure(TranExclusive(p)) = TranExclusive(p)
  BY <1>tepeq, <1>cqmsgs, <1>mi, TranClosureIdempotent
<1>knownmsgs. known \in SUBSET Messages
  <2> SUFFICES ASSUME NEW z \in known PROVE z \in Messages  OBVIOUS
  <2>1. z \in TranClosure(m)  OBVIOUS
  <2> QED BY <2>1, <1>mi, TranClosureClosed
<1>knownsub. TranClosure(known) \subseteq TranClosure(m)  BY <1>mi, <1>knownmsgs, TranClosureAbsorb
<1>tc1. TranClosure(known \cup TranExclusive(p)) = TranClosure(known) \cup TranExclusive(p)
  <2>1. TranClosure(known \cup TranExclusive(p)) = TranClosure(known) \cup TranClosure(TranExclusive(p))
    BY TranClosureUnion
  <2> QED BY <2>1, <1>tepidem
<1>tc2. TranClosure(known \cup {p}) = TranClosure(known) \cup Tran(p)
  <2>1. TranClosure(known \cup {p}) = TranClosure(known) \cup TranClosure({p})  BY TranClosureUnion
  <2>2. TranClosure({p}) = Tran(p)  BY TranClosureSingleton
  <2> QED BY <2>1, <2>2
<1>tranp. Tran(p) = {p} \cup TranExclusive(p)  BY DEF Tran, TranExclusive
<1>tc3. TranClosure(known \cup {p}) = TranClosure(known \cup TranExclusive(p)) \cup {p}
  BY <1>tc1, <1>tc2, <1>tranp
<1>oldballs. \A x \in TranClosure(known \cup TranExclusive(p)) : B(x) < bal
  BY <1>tc1, <1>knownsub, <1>tepsub
<1>ktepmsgs. TranClosure(known \cup TranExclusive(p)) \subseteq Messages
  <2> SUFFICES ASSUME NEW z \in TranClosure(known \cup TranExclusive(p)) PROVE z \in Messages  OBVIOUS
  <2>1. z \in TranClosure(m)  BY <1>tc1, <1>knownsub, <1>tepsub
  <2> QED BY <2>1, <1>mi, TranClosureClosed
<1>Vonebp. V(oneb) = V(p)  BY DEF V
<1>Vp. V(p) = V(TopLearnerMsg(m,betastar))  OBVIOUS
<1>Voneb. V(oneb) = V(TopLearnerMsg(m,betastar))  BY <1>Vonebp, <1>Vp
<1>tranoneb. Tran(oneb) = {oneb} \cup TranClosure(known \cup {p})  BY DEF TranExclusive, Tran
<1>S. Con(alpha, oneb) = ConFromCaught(alpha, CaughtS(TranClosure(m)))  BY DEF Con
<1>bsIn. betastar \in ConFromCaught(alpha, CaughtS(TranClosure(m)))  OBVIOUS
<1>xbetastarInCQ. TopLearnerMsg(m,betastar) \in CQ(m)
  <2>rel. betastar \in RelevantLearners(m)
    <3>1. \E x \in TranClosure(m) : betastar \in Lrns(x)
      <4> WITNESS TopLearnerMsg(m,betastar) \in TranClosure(m)
      <4> QED OBVIOUS
    <3> QED BY <3>1 DEF RelevantLearners
  <2> QED BY <2>rel DEF CQ
<1>xbetastarInTEp. TopLearnerMsg(m,betastar) \in TranExclusive(p)
  BY <1>xbetastarInCQ, TranClosureExpanding, <1>tepeq
<1>xbetastarInKTEp. TopLearnerMsg(m,betastar) \in TranClosure(known \cup TranExclusive(p))
  BY <1>xbetastarInTEp, TranClosureExpanding
<1>xbetastarInOneb. TopLearnerMsg(m,betastar) \in TranExclusive(oneb)
  BY <1>xbetastarInKTEp, <1>tc3
<1> SUFFICES ASSUME NEW x \in Tran(oneb)
             PROVE \/ V(x) = V(oneb)
                   \/ Con(alpha, oneb) \cap Lrns(x) = {}
                   \/ \E q \in TranExclusive(oneb) : B(q) > B(x) /\ Con(alpha, oneb) \cap Lrns(q) # {}
  BY DEF Fresh
<1>xcase. x = oneb \/ x \in TranClosure(known \cup {p})  BY <1>tranoneb
<1>caseA. CASE x = oneb  BY <1>caseA
<1>caseB. CASE x \in TranClosure(known \cup {p})
  <2>xcase2. x = p \/ x \in TranClosure(known \cup TranExclusive(p))  BY <1>caseB, <1>tc3
  <2>caseBp. CASE x = p  BY <2>caseBp, <1>Vonebp
  <2>caseBo. CASE x \in TranClosure(known \cup TranExclusive(p))
    <3>xm. x \in TranClosure(m)  BY <2>caseBo, <1>tc1, <1>knownsub, <1>tepsub
    <3>xbal. B(x) < bal  BY <2>caseBo, <1>oldballs
    <3>empty. CASE Con(alpha, oneb) \cap Lrns(x) = {}  BY <3>empty
    <3>nonempty. CASE Con(alpha, oneb) \cap Lrns(x) # {}
      <4> PICK beta \in Con(alpha, oneb) \cap Lrns(x) : TRUE  BY <3>nonempty
      <4>betaS. beta \in ConFromCaught(alpha, CaughtS(TranClosure(m)))  BY <1>S
      <4>betaLrns. beta \in Lrns(x)  OBVIOUS
      <4>xb. TopLearnerMsg(m,beta) \in TranClosure(m)
             /\ beta \in Lrns(TopLearnerMsg(m,beta))
             /\ B(x) <= B(TopLearnerMsg(m,beta))
        <5>ex. \E y \in TranClosure(m) : beta \in Lrns(y)  BY <3>xm, <4>betaLrns
        <5> QED BY <5>ex, <3>xm, <4>betaLrns, <1>mi, <1>balnat, <1>bound, TopLearnerMsgCorrect
      <4>bxbeta. B(x) <= BXBeta(m,beta)  BY <4>xb DEF BXBeta
      <4>bxbetastar. BXBeta(m,beta) <= BXBeta(m,betastar)
        <5>ex2. \E y \in TranClosure(m) : beta \in Lrns(y)  BY <3>xm, <4>betaLrns
        <5> QED BY <1>bsmax, <4>betaS, <5>ex2
      <4>xmsg. x \in Messages  BY <3>xm, <1>mi, TranClosureClosed
      <4>bxnat. B(x) \in Ballots  BY <4>xmsg, <1>mi, BBallot
      <4>bxbmsg. TopLearnerMsg(m,beta) \in Messages  BY <4>xb, <1>mi, TranClosureClosed
      <4>bxbnat. BXBeta(m,beta) \in Ballots  BY <4>bxbmsg, <1>mi, BBallot DEF BXBeta
      <4>bxbsmsg. TopLearnerMsg(m,betastar) \in TranClosure(m)  OBVIOUS
      <4>bxbsmsg2. TopLearnerMsg(m,betastar) \in Messages  BY <4>bxbsmsg, <1>mi, TranClosureClosed
      <4>bxbsnat. BXBeta(m,betastar) \in Ballots  BY <4>bxbsmsg2, <1>mi, BBallot DEF BXBeta
      <4>ineq. B(x) <= BXBeta(m,betastar)
        BY <4>bxbeta, <4>bxbetastar, <4>bxnat, <4>bxbnat, <4>bxbsnat DEF Ballots
      <4>caseTie. CASE B(x) = BXBeta(m,betastar)
        <5>eq1. B(x) = B(TopLearnerMsg(m,betastar))  BY <4>caseTie DEF BXBeta
        <5>samebal. V(x) = V(TopLearnerMsg(m,betastar))  BY <5>eq1 DEF V
        <5> QED BY <5>samebal, <1>Voneb
      <4>caseStrict. CASE B(x) < BXBeta(m,betastar)
        <5>bq. B(x) < B(TopLearnerMsg(m,betastar))  BY <4>caseStrict DEF BXBeta
        <5>lrnsx. Con(alpha, oneb) \cap Lrns(TopLearnerMsg(m,betastar)) # {}
          <6>1. betastar \in Con(alpha, oneb)  BY <1>S, <1>bsIn
          <6>2. betastar \in Lrns(TopLearnerMsg(m,betastar))  OBVIOUS
          <6> QED BY <6>1, <6>2
        <5> QED BY <1>xbetastarInOneb, <5>bq, <5>lrnsx
      <4> QED BY <4>ineq, <4>caseTie, <4>caseStrict
    <3> QED BY <3>empty, <3>nonempty
  <2> QED BY <2>xcase2, <2>caseBp, <2>caseBo
<1> QED BY <1>xcase, <1>caseA, <1>caseB

\* Degenerate case: nobody relevant to alpha attests anything in TranClosure(m)
\* at all, so clause (b) resolves every ancestor other than oneb/p (which get
\* clause (a) directly, since V(p)=V(oneb) by construction regardless of
\* which value was targeted).
LEMMA FreshOnebDegenerate ==
  ASSUME MessageInterfaceAssumptions,
         NEW m \in SUBSET Messages, NEW alpha \in Learners, NEW bal \in Ballots,
         NEW p, NEW btarg \in Ballots, NEW a \in Acceptors, NEW known \in SUBSET TranClosure(m),
         NEW oneb,
         p \in Proposals, TranExclusive(p) = TranClosure(CQ(m)), B(p) = btarg, Sig(p) \notin Acceptors,
         \A x \in TranClosure(m) : B(x) < bal, bal < btarg,
         oneb \in Messages, Sig(oneb) = a, IsOneB(oneb),
         TranExclusive(oneb) = TranClosure(known \cup {p}),
         B(oneb) = btarg,
         Caught(oneb) = CaughtS(TranClosure(m)),
         ConFromCaught(alpha, CaughtS(TranClosure(m))) \cap RelevantLearners(m) = {}
  PROVE Fresh(alpha, oneb)
<1>mi. TypeOKMessageInterface /\ TranTrans /\ TranFinite /\ AlwaysAProposal  BY DEF MessageInterfaceAssumptions
<1>balnat. bal \in Nat  BY DEF Ballots
<1>bound. \A x \in TranClosure(m) : B(x) < bal  OBVIOUS
<1>csub. CQ(m) \subseteq TranClosure(m)  BY <1>mi, <1>balnat, <1>bound, CQSubTC
<1>tepeq. TranExclusive(p) = TranClosure(CQ(m))  OBVIOUS
<1>cqmsgs. CQ(m) \in SUBSET Messages
  <2> SUFFICES ASSUME NEW z \in CQ(m) PROVE z \in Messages  OBVIOUS
  <2>1. z \in TranClosure(m)  BY <1>csub
  <2> QED BY <2>1, <1>mi, TranClosureClosed
<1>tepsub. TranExclusive(p) \subseteq TranClosure(m)  BY <1>tepeq, <1>csub, <1>cqmsgs, <1>mi, TranClosureAbsorb
<1>tepidem. TranClosure(TranExclusive(p)) = TranExclusive(p)
  BY <1>tepeq, <1>cqmsgs, <1>mi, TranClosureIdempotent
<1>knownmsgs. known \in SUBSET Messages
  <2> SUFFICES ASSUME NEW z \in known PROVE z \in Messages  OBVIOUS
  <2>1. z \in TranClosure(m)  OBVIOUS
  <2> QED BY <2>1, <1>mi, TranClosureClosed
<1>knownsub. TranClosure(known) \subseteq TranClosure(m)  BY <1>mi, <1>knownmsgs, TranClosureAbsorb
<1>tc1. TranClosure(known \cup TranExclusive(p)) = TranClosure(known) \cup TranExclusive(p)
  <2>1. TranClosure(known \cup TranExclusive(p)) = TranClosure(known) \cup TranClosure(TranExclusive(p))
    BY TranClosureUnion
  <2> QED BY <2>1, <1>tepidem
<1>tc2. TranClosure(known \cup {p}) = TranClosure(known) \cup Tran(p)
  <2>1. TranClosure(known \cup {p}) = TranClosure(known) \cup TranClosure({p})  BY TranClosureUnion
  <2>2. TranClosure({p}) = Tran(p)  BY TranClosureSingleton
  <2> QED BY <2>1, <2>2
<1>tranp. Tran(p) = {p} \cup TranExclusive(p)  BY DEF Tran, TranExclusive
<1>tc3. TranClosure(known \cup {p}) = TranClosure(known \cup TranExclusive(p)) \cup {p}
  BY <1>tc1, <1>tc2, <1>tranp
<1>Vonebp. V(oneb) = V(p)  BY DEF V
<1>tranoneb. Tran(oneb) = {oneb} \cup TranClosure(known \cup {p})  BY DEF TranExclusive, Tran
<1>S. Con(alpha, oneb) = ConFromCaught(alpha, CaughtS(TranClosure(m)))  BY DEF Con
<1> SUFFICES ASSUME NEW x \in Tran(oneb)
             PROVE \/ V(x) = V(oneb)
                   \/ Con(alpha, oneb) \cap Lrns(x) = {}
                   \/ \E q \in TranExclusive(oneb) : B(q) > B(x) /\ Con(alpha, oneb) \cap Lrns(q) # {}
  BY DEF Fresh
<1>xcase. x = oneb \/ x \in TranClosure(known \cup {p})  BY <1>tranoneb
<1>caseA. CASE x = oneb  BY <1>caseA
<1>caseB. CASE x \in TranClosure(known \cup {p})
  <2>xcase2. x = p \/ x \in TranClosure(known \cup TranExclusive(p))  BY <1>caseB, <1>tc3
  <2>caseBp. CASE x = p  BY <2>caseBp, <1>Vonebp
  <2>caseBo. CASE x \in TranClosure(known \cup TranExclusive(p))
    <3>xm. x \in TranClosure(m)  BY <2>caseBo, <1>tc1, <1>knownsub, <1>tepsub
    <3>empty. Con(alpha, oneb) \cap Lrns(x) = {}
      <4> SUFFICES ASSUME NEW beta \in Con(alpha, oneb) \cap Lrns(x) PROVE FALSE  OBVIOUS
      <4>betaS. beta \in ConFromCaught(alpha, CaughtS(TranClosure(m)))  BY <1>S
      <4>betaLearner. beta \in Learners  BY DEF Lrns
      <4>betaex. \E y \in TranClosure(m) : beta \in Lrns(y)  BY <3>xm
      <4>betaRel. beta \in RelevantLearners(m)  BY <4>betaLearner, <4>betaex DEF RelevantLearners
      <4> QED BY <4>betaS, <4>betaRel
    <3> QED BY <3>empty
  <2> QED BY <2>xcase2, <2>caseBp, <2>caseBo
<1> QED BY <1>xcase, <1>caseA, <1>caseB

\* --- lean wrappers: bundle OneBExists+FreshOneb / FreshOnebDegenerate behind a
\* small clean-context ASSUME so citing them from the (much heavier)
\* DecideableProposalExists context doesn't exhaust the backend's search
\* (see SKILL.md 8: "many NEW-bound variables ... can exhaust Zenon's resources").
LEMMA OneBFresh ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions,
         NEW m \in SUBSET Messages, NEW alpha \in Learners, NEW p \in Proposals,
         \E bal \in Ballots, btarg \in Ballots, betastar \in Learners :
           /\ TranExclusive(p) = TranClosure(CQ(m))
           /\ B(p) = btarg
           /\ Sig(p) \notin Acceptors
           /\ (\A x \in TranClosure(m) : B(x) < bal)
           /\ bal < btarg
           /\ betastar \in ConFromCaught(alpha, CaughtS(TranClosure(m)))
           /\ TopLearnerMsg(m,betastar) \in TranClosure(m)
           /\ betastar \in Lrns(TopLearnerMsg(m,betastar))
           /\ (\A beta \in ConFromCaught(alpha, CaughtS(TranClosure(m))) :
                (\E x \in TranClosure(m) : beta \in Lrns(x)) => BXBeta(m,beta) <= BXBeta(m,betastar))
           /\ V(p) = V(TopLearnerMsg(m,betastar))
  PROVE \A a \in Acceptors :
          \A known \in SUBSET TranClosure(m) :
            (/\ IsFiniteSet(known) /\ a \notin CaughtS(TranClosure(known \cup TranExclusive(p))))
            => \E oneb \in Messages :
                 (/\ Sig(oneb) = a /\ a \notin Caught(oneb) /\ IsOneB(oneb)
                  /\ TranExclusive(oneb) = TranClosure(known \cup {p}) /\ Fresh(alpha, oneb))
<1> PICK bal \in Ballots, btarg \in Ballots, betastar \in Learners :
      /\ TranExclusive(p) = TranClosure(CQ(m))
      /\ B(p) = btarg
      /\ Sig(p) \notin Acceptors
      /\ (\A x \in TranClosure(m) : B(x) < bal)
      /\ bal < btarg
      /\ betastar \in ConFromCaught(alpha, CaughtS(TranClosure(m)))
      /\ TopLearnerMsg(m,betastar) \in TranClosure(m)
      /\ betastar \in Lrns(TopLearnerMsg(m,betastar))
      /\ (\A beta \in ConFromCaught(alpha, CaughtS(TranClosure(m))) :
           (\E x \in TranClosure(m) : beta \in Lrns(x)) => BXBeta(m,beta) <= BXBeta(m,betastar))
      /\ V(p) = V(TopLearnerMsg(m,betastar))
  OBVIOUS
<1> SUFFICES ASSUME NEW a \in Acceptors, NEW known \in SUBSET TranClosure(m),
                    IsFiniteSet(known), a \notin CaughtS(TranClosure(known \cup TranExclusive(p)))
             PROVE \E oneb \in Messages :
                     (/\ Sig(oneb) = a /\ a \notin Caught(oneb) /\ IsOneB(oneb)
                      /\ TranExclusive(oneb) = TranClosure(known \cup {p}) /\ Fresh(alpha, oneb))
  OBVIOUS
<1>oex. \E oneb \in Messages :
          /\ Sig(oneb) = a
          /\ a \notin Caught(oneb)
          /\ IsOneB(oneb)
          /\ TranExclusive(oneb) = TranClosure(known \cup {p})
          /\ B(oneb) = btarg
          /\ Caught(oneb) = CaughtS(TranClosure(m))
  BY LearnerGraphAssumptions, OneBExists
<1> PICK oneb \in Messages :
      /\ Sig(oneb) = a
      /\ a \notin Caught(oneb)
      /\ IsOneB(oneb)
      /\ TranExclusive(oneb) = TranClosure(known \cup {p})
      /\ B(oneb) = btarg
      /\ Caught(oneb) = CaughtS(TranClosure(m))
  BY <1>oex
<1>fresh. Fresh(alpha, oneb)
  BY LearnerGraphAssumptions, FreshOneb
<1> QED BY <1>fresh

LEMMA OneBFreshDegenerate ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions,
         NEW m \in SUBSET Messages, NEW alpha \in Learners, NEW p \in Proposals,
         \E bal \in Ballots, btarg \in Ballots :
           /\ TranExclusive(p) = TranClosure(CQ(m))
           /\ B(p) = btarg
           /\ Sig(p) \notin Acceptors
           /\ (\A x \in TranClosure(m) : B(x) < bal)
           /\ bal < btarg,
         ConFromCaught(alpha, CaughtS(TranClosure(m))) \cap RelevantLearners(m) = {}
  PROVE \A a \in Acceptors :
          \A known \in SUBSET TranClosure(m) :
            (/\ IsFiniteSet(known) /\ a \notin CaughtS(TranClosure(known \cup TranExclusive(p))))
            => \E oneb \in Messages :
                 (/\ Sig(oneb) = a /\ a \notin Caught(oneb) /\ IsOneB(oneb)
                  /\ TranExclusive(oneb) = TranClosure(known \cup {p}) /\ Fresh(alpha, oneb))
<1> PICK bal \in Ballots, btarg \in Ballots :
      /\ TranExclusive(p) = TranClosure(CQ(m))
      /\ B(p) = btarg
      /\ Sig(p) \notin Acceptors
      /\ (\A x \in TranClosure(m) : B(x) < bal)
      /\ bal < btarg
  OBVIOUS
<1> SUFFICES ASSUME NEW a \in Acceptors, NEW known \in SUBSET TranClosure(m),
                    IsFiniteSet(known), a \notin CaughtS(TranClosure(known \cup TranExclusive(p)))
             PROVE \E oneb \in Messages :
                     (/\ Sig(oneb) = a /\ a \notin Caught(oneb) /\ IsOneB(oneb)
                      /\ TranExclusive(oneb) = TranClosure(known \cup {p}) /\ Fresh(alpha, oneb))
  OBVIOUS
<1>oex. \E oneb \in Messages :
          /\ Sig(oneb) = a
          /\ a \notin Caught(oneb)
          /\ IsOneB(oneb)
          /\ TranExclusive(oneb) = TranClosure(known \cup {p})
          /\ B(oneb) = btarg
          /\ Caught(oneb) = CaughtS(TranClosure(m))
  BY LearnerGraphAssumptions, OneBExists
<1> PICK oneb \in Messages :
      /\ Sig(oneb) = a
      /\ a \notin Caught(oneb)
      /\ IsOneB(oneb)
      /\ TranExclusive(oneb) = TranClosure(known \cup {p})
      /\ B(oneb) = btarg
      /\ Caught(oneb) = CaughtS(TranClosure(m))
  BY <1>oex
<1>fresh. Fresh(alpha, oneb)
  BY FreshOnebDegenerate
<1> QED BY <1>fresh

DecideableProposalTranExclusive(mm) == TranClosure(CQ(mm))

DecideableProposalV(alpha, bal, mm) ==
  LET S  == ConFromCaught(alpha, CaughtS(TranClosure(mm)))
      SS == S \cap RelevantLearners(mm)
  IN  IF SS = {}
      THEN BalToVal(bal)
      ELSE LET betastar == CHOOSE beta \in SS : \A gamma \in SS : BXBeta(mm,gamma) <= BXBeta(mm,beta)
           IN V(TopLearnerMsg(mm, betastar))

LEMMA DecideableProposalPExists ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions, ValueInterfaceAssumptions,
         NEW alpha \in Learners, NEW bal \in Ballots, NEW m \in SUBSET Messages,
         alpha \in ConFromCaught(alpha, CaughtS(TranClosure(m))),
         \A x \in TranClosure(m) : B(x) < bal
  PROVE \E p \in Proposals :
          /\ TranExclusive(p) = DecideableProposalTranExclusive(m)
          /\ B(p) > bal
          /\ Sig(p) \notin Acceptors
          /\ V(p) = DecideableProposalV(alpha, bal, m)
<1>mi. TypeOKMessageInterface /\ TranTrans /\ TranFinite /\ AlwaysAProposal  BY DEF MessageInterfaceAssumptions
<1>via. AlwaysAValue  BY DEF ValueInterfaceAssumptions
<1>balnat. bal \in Nat  BY DEF Ballots
<1>bound. \A x \in TranClosure(m) : B(x) < bal  OBVIOUS
<1> DEFINE S == ConFromCaught(alpha, CaughtS(TranClosure(m)))
<1> DEFINE SS == S \cap RelevantLearners(m)
<1>sL. S \subseteq Learners  BY DEF ConFromCaught
<1>caseNE. CASE SS # {}
  <2>ssL. SS \in SUBSET Learners
    <3>1. RelevantLearners(m) \subseteq Learners  BY DEF RelevantLearners
    <3> QED BY <3>1
  <2>ssrel. \A beta \in SS : \E x \in TranClosure(m) : beta \in Lrns(x)
    <3> SUFFICES ASSUME NEW beta \in SS PROVE \E x \in TranClosure(m) : beta \in Lrns(x)  OBVIOUS
    <3>1. beta \in RelevantLearners(m)  OBVIOUS
    <3> QED BY <3>1 DEF RelevantLearners
  <2>bse. \E beta \in SS : \A gamma \in SS : BXBeta(m,gamma) <= BXBeta(m,beta)
    BY <2>ssL, <1>caseNE, <2>ssrel, <1>balnat, <1>bound, BetaStarExists
  <2> DEFINE betastar == CHOOSE beta \in SS : \A gamma \in SS : BXBeta(m,gamma) <= BXBeta(m,beta)
  <2>bsprop. betastar \in SS /\ (\A gamma \in SS : BXBeta(m,gamma) <= BXBeta(m,betastar))
    BY <2>bse
  <2>bsS. betastar \in S  BY <2>bsprop
  <2>bsRel. betastar \in RelevantLearners(m)  BY <2>bsprop
  <2>bsLrns. betastar \in Lrns(TopLearnerMsg(m,betastar))
    <3>ex. \E x \in TranClosure(m) : betastar \in Lrns(x)  BY <2>bsRel DEF RelevantLearners
    <3> QED BY <3>ex, <1>mi, <1>balnat, <1>bound, TopLearnerMsgCorrect
  <2>xbmsgs. TopLearnerMsg(m,betastar) \in TranClosure(m)
    <3>ex. \E x \in TranClosure(m) : betastar \in Lrns(x)  BY <2>bsRel DEF RelevantLearners
    <3> QED BY <3>ex, <1>mi, <1>balnat, <1>bound, TopLearnerMsgCorrect
  <2>xbm. TopLearnerMsg(m,betastar) \in Messages  BY <2>xbmsgs, <1>mi, TranClosureClosed
  <2>vval. V(TopLearnerMsg(m,betastar)) \in Values
    <3>1. B(TopLearnerMsg(m,betastar)) \in Ballots  BY <2>xbm, <1>mi, BBallot
    <3> QED BY <3>1, <1>via DEF V, AlwaysAValue
  <2>dpv. DecideableProposalV(alpha,bal,m) = V(TopLearnerMsg(m,betastar))
    BY <1>caseNE DEF DecideableProposalV
  <2>pex. \E p \in Proposals :
            /\ TranExclusive(p) = TranClosure(CQ(m))
            /\ B(p) > bal
            /\ Sig(p) \notin Acceptors
            /\ V(p) = V(TopLearnerMsg(m,betastar))
    BY <1>mi, LearnerGraphAssumptions, ValueInterfaceAssumptions, <2>vval, PExists
  <2> QED BY <2>pex, <2>dpv DEF DecideableProposalTranExclusive
<1>caseE. CASE SS = {}
  <2>vval. BalToVal(bal) \in Values  BY <1>via DEF AlwaysAValue
  <2>dpv. DecideableProposalV(alpha,bal,m) = BalToVal(bal)  BY <1>caseE DEF DecideableProposalV
  <2>pex. \E p \in Proposals :
            /\ TranExclusive(p) = TranClosure(CQ(m))
            /\ B(p) > bal
            /\ Sig(p) \notin Acceptors
            /\ V(p) = BalToVal(bal)
    BY <1>mi, LearnerGraphAssumptions, ValueInterfaceAssumptions, <2>vval, PExists
  <2> QED BY <2>pex, <2>dpv DEF DecideableProposalTranExclusive
<1> QED BY <1>caseNE, <1>caseE

\* Any-witness companion to DecideableProposalOneBExists: given a message oneb
\* (not necessarily the one OneBExists/AlwaysANewOneB happens to construct)
\* whose TranExclusive matches the known-plus-p shape, oneb's B/IsOneB/Fresh
\* are all determined purely by that shape -- independent of how oneb came to
\* exist. This is what lets the *actual* network-constructed witness (from
\* AlwaysOneBInvariant's machinery, which goes through a different existence
\* path than OneBExists) still be shown depth-0-eligible.
LEMMA DecideableProposalOneBFreshAny ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions, ValueInterfaceAssumptions,
         NEW alpha \in Learners, NEW bal \in Ballots, NEW m \in SUBSET Messages,
         alpha \in ConFromCaught(alpha, CaughtS(TranClosure(m))),
         \A x \in TranClosure(m) : B(x) < bal,
         NEW p \in Proposals,
         TranExclusive(p) = DecideableProposalTranExclusive(m),
         B(p) > bal,
         Sig(p) \notin Acceptors,
         V(p) = DecideableProposalV(alpha, bal, m),
         NEW known \in SUBSET TranClosure(m),
         NEW a \in Acceptors, NEW oneb \in (Messages \ Proposals), Sig(oneb) = a,
         TranExclusive(oneb) = TranClosure(known \cup {p}),
         Sig(oneb) \notin CaughtS(TranClosure(known \cup TranExclusive(p)))
  PROVE /\ B(oneb) = B(p)
        /\ IsOneB(oneb)
        /\ Fresh(alpha, oneb)
<1>mi. TypeOKMessageInterface /\ TranTrans /\ TranFinite /\ AlwaysAProposal
  BY DEF MessageInterfaceAssumptions
<1>pmsg. p \in Messages  BY <1>mi DEF TypeOKMessageInterface
<1>btnat. B(p) \in Ballots  BY <1>pmsg, <1>mi, BBallot
<1> DEFINE btarg == B(p)
<1>balnat. bal \in Nat  BY DEF Ballots
<1>bound. \A x \in TranClosure(m) : B(x) < bal  OBVIOUS
<1>baltbarg. bal < btarg  OBVIOUS
<1>tepeq. TranExclusive(p) = TranClosure(CQ(m))  BY DEF DecideableProposalTranExclusive
<1>csub. CQ(m) \subseteq TranClosure(m)  BY <1>mi, <1>balnat, <1>bound, CQSubTC
<1>cqmsgs. CQ(m) \in SUBSET Messages
  <2> SUFFICES ASSUME NEW z \in CQ(m) PROVE z \in Messages  OBVIOUS
  <2>1. z \in TranClosure(m)  BY <1>csub
  <2> QED BY <2>1, <1>mi, TranClosureClosed
<1>tepsub. TranExclusive(p) \subseteq TranClosure(m)  BY <1>tepeq, <1>csub, <1>cqmsgs, <1>mi, TranClosureAbsorb
<1>tepidem. TranClosure(TranExclusive(p)) = TranExclusive(p)
  BY <1>tepeq, <1>cqmsgs, <1>mi, TranClosureIdempotent
<1>knownmsgs. known \in SUBSET Messages
  <2> SUFFICES ASSUME NEW z \in known PROVE z \in Messages  OBVIOUS
  <2>1. z \in TranClosure(m)  OBVIOUS
  <2> QED BY <2>1, <1>mi, TranClosureClosed
<1>knownsub. TranClosure(known) \subseteq TranClosure(m)  BY <1>mi, <1>knownmsgs, TranClosureAbsorb
<1>tc1. TranClosure(known \cup TranExclusive(p)) = TranClosure(known) \cup TranExclusive(p)
  <2>1. TranClosure(known \cup TranExclusive(p)) = TranClosure(known) \cup TranClosure(TranExclusive(p))
    BY TranClosureUnion
  <2> QED BY <2>1, <1>tepidem
<1>tc2. TranClosure(known \cup {p}) = TranClosure(known) \cup Tran(p)
  <2>1. TranClosure(known \cup {p}) = TranClosure(known) \cup TranClosure({p})  BY TranClosureUnion
  <2>2. TranClosure({p}) = Tran(p)  BY TranClosureSingleton
  <2> QED BY <2>1, <2>2
<1>tranp. Tran(p) = {p} \cup TranExclusive(p)  BY DEF Tran, TranExclusive
<1>tc3. TranClosure(known \cup {p}) = TranClosure(known \cup TranExclusive(p)) \cup {p}
  BY <1>tc1, <1>tc2, <1>tranp
<1>oldballs. \A x \in TranClosure(known \cup TranExclusive(p)) : B(x) < bal
  BY <1>tc1, <1>knownsub, <1>tepsub
<1>ktepmsgs. TranClosure(known \cup TranExclusive(p)) \subseteq Messages
  <2> SUFFICES ASSUME NEW z \in TranClosure(known \cup TranExclusive(p)) PROVE z \in Messages  OBVIOUS
  <2>1. z \in TranClosure(m)  BY <1>tc1, <1>knownsub, <1>tepsub
  <2> QED BY <2>1, <1>mi, TranClosureClosed
<1>kpmsgs. TranClosure(known \cup {p}) \subseteq Messages  BY <1>tc3, <1>ktepmsgs, <1>pmsg
<1>onebnotprop. oneb \notin Proposals  OBVIOUS
<1>onebmsg. oneb \in Messages  OBVIOUS
<1>pnotoneb. p # oneb  BY <1>onebnotprop
<1>cqoldballs. \A x \in TranClosure(CQ(m)) : B(x) < btarg
  <2> SUFFICES ASSUME NEW x \in TranClosure(CQ(m)) PROVE B(x) < btarg  OBVIOUS
  <2>1. x \in TranClosure(m)  BY <1>csub, <1>mi, <1>cqmsgs, TranClosureAbsorb
  <2>2. B(x) < bal  BY <2>1, <1>bound
  <2>3. B(x) \in Ballots  BY <2>1, <1>mi, TranClosureClosed, BBallot
  <2> QED BY <2>2, <2>3, <1>baltbarg, <1>balnat, <1>btnat DEF Ballots
<1>bpbtarg. B(p) = btarg  OBVIOUS
<1>pbalp. ProposalBal(p) = btarg
  <2>propsub. Proposals \subseteq Messages  BY <1>mi DEF TypeOKMessageInterface
  <2>pgp. p \in GetProposals(p)
    <3>1. p \in Tran(p)  BY DEF Tran
    <3> QED BY <3>1 DEF GetProposals
  <2>fin. IsFiniteSet(GetProposals(p))
    <3>1. GetProposals(p) \subseteq Tran(p)  BY DEF GetProposals
    <3>2. IsFiniteSet(Tran(p))  BY <1>pmsg, <1>mi DEF TranFinite
    <3> QED BY <3>1, <3>2, FS_Subset
  <2>ne. GetProposals(p) # {}  BY <2>pgp
  <2>sub. GetProposals(p) \subseteq Proposals  BY DEF GetProposals
  <2>choose. /\ B(p) \in {ProposalBal(z) : z \in GetProposals(p)}
             /\ \A w \in {ProposalBal(z) : z \in GetProposals(p)} : B(p) >= w
    BY <1>mi, <2>fin, <2>sub, <2>ne, MaxBSetProperty DEF B
  <2> PICK z \in GetProposals(p) : B(p) = ProposalBal(z)  BY <2>choose
  <2>zgp. z \in Proposals /\ z \in Tran(p)  BY DEF GetProposals
  <2>zcase. z = p \/ z \in TranExclusive(p)  BY <2>zgp DEF TranExclusive
  <2>notother. z \in TranExclusive(p) => FALSE
    <3> SUFFICES ASSUME z \in TranExclusive(p) PROVE FALSE  OBVIOUS
    <3>1. z \in TranClosure(CQ(m))  BY <1>tepeq
    <3>2. B(z) < btarg  BY <3>1, <1>cqoldballs
    <3>3. ProposalBal(z) <= B(z)  BY <2>zgp, ProposalBalLeB
    <3>4. ProposalBal(z) = B(p)  BY <2>choose
    <3>5. B(p) = btarg  OBVIOUS
    <3>zmsg. z \in Messages  BY <2>zgp, <1>mi DEF TypeOKMessageInterface
    <3>pbz. ProposalBal(z) \in Ballots  BY <2>zgp, <1>mi DEF TypeOKMessageInterface, ProposalBal
    <3>bz. B(z) \in Ballots  BY <3>zmsg, <1>mi, BBallot
    <3>bp. B(p) \in Ballots  BY <1>btnat
    <3> QED BY <3>2, <3>3, <3>4, <3>5, <3>pbz, <3>bz, <3>bp DEF Ballots
  <2>zisp. z = p  BY <2>zcase, <2>notother
  <2> QED BY <2>choose, <2>zisp
<1>notpballs. \A x \in TranClosure(known \cup {p}) : x # p => B(x) < btarg
  <2> SUFFICES ASSUME NEW x \in TranClosure(known \cup {p}), x # p PROVE B(x) < btarg  OBVIOUS
  <2>1. x \in TranClosure(known \cup TranExclusive(p))  BY <1>tc3
  <2>2. B(x) < bal  BY <2>1, <1>oldballs
  <2>3. x \in Messages  BY <2>1, <1>ktepmsgs
  <2>4. B(x) \in Ballots  BY <2>3, <1>mi, BBallot
  <2> QED BY <2>2, <2>4, <1>baltbarg, <1>balnat, <1>btnat DEF Ballots
<1>pinS. p \in TranClosure(known \cup {p})
  <2>1. p \in Tran(p)  BY DEF Tran
  <2> QED BY <2>1 DEF TranClosure
<1>Boneb. B(oneb) = btarg
  BY <1>onebmsg, <1>kpmsgs, <1>onebnotprop, <1>pinS, <1>pbalp, <1>notpballs, <1>btnat, BOfAbsorbing
<1>seteqp. {x \in TranClosure(known \cup {p}) : B(x) = btarg} = {p}
  <2> SUFFICES ASSUME NEW x \in TranClosure(known \cup {p}), B(x) = btarg
               PROVE x = p
    BY <1>tc3
  <2>1. x \in TranClosure(known \cup TranExclusive(p)) \/ x = p  BY <1>tc3
  <2>2. CASE x = p  BY <2>2
  <2>3. CASE x \in TranClosure(known \cup TranExclusive(p))
    <3>1. B(x) < bal  BY <2>3, <1>oldballs
    <3>2. x \in Messages  BY <2>3, <1>ktepmsgs
    <3>3. B(x) \in Ballots  BY <3>2, <1>mi, BBallot
    <3> QED BY <3>1, <3>3, <1>baltbarg, <1>balnat, <1>btnat DEF Ballots
  <2> QED BY <2>1, <2>2, <2>3
<1>tranoneb. Tran(oneb) = {oneb} \cup TranClosure(known \cup {p})  BY DEF Tran, TranExclusive
<1>cardoneb2. Cardinality({z \in Tran(oneb) : B(z) = btarg}) = 2
  <2>seteq. {z \in Tran(oneb) : B(z) = btarg} = {oneb, p}
    BY <1>tranoneb, <1>seteqp, <1>Boneb, <1>pnotoneb
  <2>card2. Cardinality({oneb, p}) = 2
    <3>1. IsFiniteSet({p})  BY FS_Singleton
    <3>2. Cardinality({p}) = 1  BY FS_Singleton
    <3>3. oneb \notin {p}  BY <1>pnotoneb
    <3>4. {oneb,p} = {oneb} \cup {p}  OBVIOUS
    <3> QED BY <3>1, <3>2, <3>3, <3>4, FS_AddElement
  <2> QED BY <2>seteq, <2>card2
<1>isoneb. IsOneB(oneb)
  <2>1. {z \in Tran(oneb) : B(z) = B(oneb)} = {z \in Tran(oneb) : B(z) = btarg}  BY <1>Boneb
  <2>2. Cardinality({z \in Tran(oneb) : B(z) = B(oneb)}) = 2  BY <2>1, <1>cardoneb2
  <2>3. ~IsProposal(oneb)  BY <1>onebnotprop DEF IsProposal
  <2> QED BY <2>3, <2>2 DEF IsOneB
<1>caughtoneb. Caught(oneb) = CaughtS(TranClosure(m))
  <2>ctran. Tran(oneb) = {oneb} \cup TranClosure(known \cup {p})  BY <1>tranoneb
  <2>step1. CaughtS(TranClosure(known \cup TranExclusive(p))) = CaughtS(TranClosure(m))
    <3>sub1. TranClosure(known \cup TranExclusive(p)) \subseteq TranClosure(m)
      BY <1>tc1, <1>knownsub, <1>tepsub
    <3>fwd. CaughtS(TranClosure(known \cup TranExclusive(p))) \subseteq CaughtS(TranClosure(m))
      BY <3>sub1 DEF CaughtS
    <3>bwd. CaughtS(TranClosure(m)) \subseteq CaughtS(TranClosure(known \cup TranExclusive(p)))
      <4> SUFFICES ASSUME NEW s \in CaughtS(TranClosure(m))
                   PROVE s \in CaughtS(TranClosure(known \cup TranExclusive(p)))
        OBVIOUS
      <4>w1. s \in CaughtAcc(m)  BY DEF CaughtAcc
      <4>w2. CatchWitness1(m,s) \in CQ(m) /\ CatchWitness2(m,s) \in CQ(m)  BY <4>w1 DEF CQ
      <4>w3. CatchWitness1(m,s) \in TranClosure(CQ(m)) /\ CatchWitness2(m,s) \in TranClosure(CQ(m))
        BY <4>w2, TranClosureExpanding
      <4>w4. CatchWitness1(m,s) \in TranExclusive(p) /\ CatchWitness2(m,s) \in TranExclusive(p)
        BY <4>w3, <1>tepeq
      <4>w5. /\ Sig(CatchWitness1(m,s)) = s /\ Sig(CatchWitness2(m,s)) = s
             /\ CatchWitness1(m,s) \notin Tran(CatchWitness2(m,s))
             /\ CatchWitness2(m,s) \notin Tran(CatchWitness1(m,s))
        BY <1>mi, <4>w1, CatchWitnessCorrect DEF CaughtAcc
      <4>w6. CatchWitness1(m,s) \in TranClosure(known \cup TranExclusive(p))
             /\ CatchWitness2(m,s) \in TranClosure(known \cup TranExclusive(p))
        BY <4>w4, TranClosureExpanding
      <4> QED BY <4>w5, <4>w6 DEF CaughtS
    <3> QED BY <3>fwd, <3>bwd
  <2>step2. CaughtS(TranClosure(known \cup {p})) = CaughtS(TranClosure(known \cup TranExclusive(p)))
    <3>1. CaughtS(TranClosure(known \cup {p})) = CaughtS(TranClosure(known \cup TranExclusive(p)) \cup {p})
      BY <1>tc3
    <3>2. CaughtS(TranClosure(known \cup TranExclusive(p)) \cup {p})
            = CaughtS(TranClosure(known \cup TranExclusive(p)))
      BY <1>mi, <1>ktepmsgs, CaughtSAddNonAcceptor
    <3> QED BY <3>1, <3>2
  <2>step3. CaughtS({oneb} \cup TranClosure(known \cup {p})) = CaughtS(TranClosure(known \cup {p}))
    <3>comm. {oneb} \cup TranClosure(known \cup {p}) = TranClosure(known \cup {p}) \cup {oneb}  OBVIOUS
    <3>anot. Sig(oneb) \notin CaughtS(TranClosure(known \cup {p}))  BY <2>step2
    <3>anotoneb. Sig(oneb) \notin CaughtS(TranClosure(known \cup {p}) \cup {oneb})
      <4> SUFFICES ASSUME Sig(oneb) \in CaughtS(TranClosure(known \cup {p}) \cup {oneb}) PROVE FALSE
        OBVIOUS
      <4>1. PICK m1 \in (TranClosure(known \cup {p}) \cup {oneb}) :
              \E m2 \in (TranClosure(known \cup {p}) \cup {oneb}) :
                Sig(m1) = Sig(oneb) /\ Sig(m2) = Sig(oneb) /\ m1 \notin Tran(m2) /\ m2 \notin Tran(m1)
        BY DEF CaughtS
      <4>2. PICK m2 \in (TranClosure(known \cup {p}) \cup {oneb}) :
              Sig(m1) = Sig(oneb) /\ Sig(m2) = Sig(oneb) /\ m1 \notin Tran(m2) /\ m2 \notin Tran(m1)
        BY <4>1
      <4>m1case. m1 = oneb \/ m1 \in TranClosure(known \cup {p})  BY <4>2
      <4>m2case. m2 = oneb \/ m2 \in TranClosure(known \cup {p})  BY <4>2
      <4>notboth. ~(m1 = oneb /\ m2 = oneb)
        <5> SUFFICES ASSUME m1 = oneb, m2 = oneb PROVE FALSE  OBVIOUS
        <5>1. m1 \in Tran(m2)  BY DEF Tran
        <5> QED BY <5>1, <4>2
      <4>m1oneb. CASE m1 = oneb
        <5>m2old. m2 \in TranClosure(known \cup {p})  BY <4>m1oneb, <4>notboth, <4>m2case
        <5>m2te. m2 \in TranExclusive(oneb)  BY <5>m2old
        <5>m2tr. m2 \in Tran(oneb)  BY <5>m2te DEF TranExclusive
        <5>m2trm1. m2 \in Tran(m1)  BY <5>m2tr, <4>m1oneb
        <5> QED BY <5>m2trm1, <4>2
      <4>m2oneb. CASE m2 = oneb
        <5>m1old. m1 \in TranClosure(known \cup {p})  BY <4>m2oneb, <4>notboth, <4>m1case
        <5>m1te. m1 \in TranExclusive(oneb)  BY <5>m1old
        <5>m1tr. m1 \in Tran(oneb)  BY <5>m1te DEF TranExclusive
        <5>m1trm2. m1 \in Tran(m2)  BY <5>m1tr, <4>m2oneb
        <5> QED BY <5>m1trm2, <4>2
      <4>bothold. CASE m1 \in TranClosure(known \cup {p}) /\ m2 \in TranClosure(known \cup {p})
        <5>caught. Sig(oneb) \in CaughtS(TranClosure(known \cup {p}))
          BY <4>2, <4>bothold DEF CaughtS
        <5> QED BY <5>caught, <3>anot
      <4>alldisj. m1 = oneb \/ m2 = oneb
                    \/ (m1 \in TranClosure(known \cup {p}) /\ m2 \in TranClosure(known \cup {p}))
        BY <4>m1case, <4>m2case
      <4> QED BY <4>alldisj, <4>m1oneb, <4>m2oneb, <4>bothold
    <3>eq. CaughtS(TranClosure(known \cup {p}) \cup {oneb}) = CaughtS(TranClosure(known \cup {p}))
      <4>facc. Sig(oneb) \in Acceptors \/ Sig(oneb) \notin Acceptors  OBVIOUS
      <4>a. CASE Sig(oneb) \in Acceptors
        BY <1>mi, <1>kpmsgs, <3>anotoneb, <4>a, CaughtSAddOne
      <4>b. CASE Sig(oneb) \notin Acceptors
        BY <1>mi, <1>kpmsgs, <4>b, CaughtSAddNonAcceptor
      <4> QED BY <4>facc, <4>a, <4>b
    <3> QED BY <3>comm, <3>eq
  <2> QED BY <2>ctran, <2>step1, <2>step2, <2>step3 DEF Caught
<1> DEFINE S == ConFromCaught(alpha, CaughtS(TranClosure(m)))
<1> DEFINE SS == S \cap RelevantLearners(m)
<1>fresh. Fresh(alpha, oneb)
  <2>caseNE. CASE SS # {}
    <3>ssL. SS \in SUBSET Learners
      <4>1. RelevantLearners(m) \subseteq Learners  BY DEF RelevantLearners
      <4> QED BY <4>1
    <3>ssrel. \A beta \in SS : \E x \in TranClosure(m) : beta \in Lrns(x)
      <4> SUFFICES ASSUME NEW beta \in SS PROVE \E x \in TranClosure(m) : beta \in Lrns(x)  OBVIOUS
      <4>1. beta \in RelevantLearners(m)  OBVIOUS
      <4> QED BY <4>1 DEF RelevantLearners
    <3>bse. \E beta \in SS : \A gamma \in SS : BXBeta(m,gamma) <= BXBeta(m,beta)
      BY <3>ssL, <2>caseNE, <3>ssrel, <1>balnat, <1>bound, BetaStarExists
    <3> DEFINE betastar == CHOOSE beta \in SS : \A gamma \in SS : BXBeta(m,gamma) <= BXBeta(m,beta)
    <3>bsprop. betastar \in SS /\ (\A gamma \in SS : BXBeta(m,gamma) <= BXBeta(m,betastar))
      BY <3>bse
    <3>bsS. betastar \in S  BY <3>bsprop
    <3>bsSraw. betastar \in ConFromCaught(alpha, CaughtS(TranClosure(m)))  BY <3>bsS
    <3>bsRel. betastar \in RelevantLearners(m)  BY <3>bsprop
    <3>bstL. betastar \in Learners  BY <3>ssL, <3>bsprop
    <3>bsLrns. betastar \in Lrns(TopLearnerMsg(m,betastar))
      <4>ex. \E x \in TranClosure(m) : betastar \in Lrns(x)  BY <3>bsRel DEF RelevantLearners
      <4> QED BY <4>ex, <1>mi, <1>balnat, <1>bound, TopLearnerMsgCorrect
    <3>bsMax. \A beta \in S : (\E x \in TranClosure(m) : beta \in Lrns(x)) => BXBeta(m,beta) <= BXBeta(m,betastar)
      <4> SUFFICES ASSUME NEW beta \in S, \E x \in TranClosure(m) : beta \in Lrns(x)
                   PROVE BXBeta(m,beta) <= BXBeta(m,betastar)
        OBVIOUS
      <4>0. beta \in Learners  BY DEF ConFromCaught
      <4>1. beta \in RelevantLearners(m)  BY <4>0 DEF RelevantLearners
      <4>2. beta \in SS  BY <4>1
      <4> QED BY <4>2, <3>bsprop
    <3>bsMaxraw. \A beta \in ConFromCaught(alpha, CaughtS(TranClosure(m))) :
                   (\E x \in TranClosure(m) : beta \in Lrns(x)) => BXBeta(m,beta) <= BXBeta(m,betastar)
      BY <3>bsMax
    <3>xbmsgs. TopLearnerMsg(m,betastar) \in TranClosure(m)
      <4>ex. \E x \in TranClosure(m) : betastar \in Lrns(x)  BY <3>bsRel DEF RelevantLearners
      <4> QED BY <4>ex, <1>mi, <1>balnat, <1>bound, TopLearnerMsgCorrect
    <3>dpv. DecideableProposalV(alpha,bal,m) = V(TopLearnerMsg(m,betastar))
      BY <2>caseNE DEF DecideableProposalV
    <3>vp. V(p) = V(TopLearnerMsg(m,betastar))  BY <3>dpv
    <3>bsWit. \E bs \in Learners : bs = betastar  BY <3>bstL
    <3> PICK bs \in Learners : bs = betastar  BY <3>bsWit
    <3>bsSraw2. bs \in ConFromCaught(alpha, CaughtS(TranClosure(m)))  BY <3>bsSraw
    <3>xbmsgs2. TopLearnerMsg(m,bs) \in TranClosure(m)  BY <3>xbmsgs
    <3>bsLrns2. bs \in Lrns(TopLearnerMsg(m,bs))  BY <3>bsLrns
    <3>bsMaxraw2. \A beta \in ConFromCaught(alpha, CaughtS(TranClosure(m))) :
                   (\E x \in TranClosure(m) : beta \in Lrns(x)) => BXBeta(m,beta) <= BXBeta(m,bs)
      BY <3>bsMaxraw
    <3>vp2. V(p) = V(TopLearnerMsg(m,bs))  BY <3>vp
    <3>bsRel2. bs \in RelevantLearners(m)  BY <3>bsRel
    <3>Vonebp. V(oneb) = V(p)  BY <1>Boneb, <1>bpbtarg DEF V
    <3>Voneb. V(oneb) = V(TopLearnerMsg(m,bs))  BY <3>Vonebp, <3>vp2
    <3>S. Con(alpha, oneb) = ConFromCaught(alpha, CaughtS(TranClosure(m)))  BY <1>caughtoneb DEF Con
    <3>bsIn. bs \in ConFromCaught(alpha, CaughtS(TranClosure(m)))  BY <3>bsSraw2
    <3>xbetastarInCQ. TopLearnerMsg(m,bs) \in CQ(m)
      <4>rel. bs \in RelevantLearners(m)  BY <3>bsRel2
      <4> QED BY <4>rel DEF CQ
    <3>xbetastarInTEp. TopLearnerMsg(m,bs) \in TranExclusive(p)
      BY <3>xbetastarInCQ, TranClosureExpanding, <1>tepeq
    <3>xbetastarInKTEp. TopLearnerMsg(m,bs) \in TranClosure(known \cup TranExclusive(p))
      BY <3>xbetastarInTEp, TranClosureExpanding
    <3>xbetastarInOneb. TopLearnerMsg(m,bs) \in TranExclusive(oneb)
      BY <3>xbetastarInKTEp, <1>tc3
    <3> SUFFICES ASSUME NEW x \in Tran(oneb)
                 PROVE \/ V(x) = V(oneb)
                       \/ Con(alpha, oneb) \cap Lrns(x) = {}
                       \/ \E q \in TranExclusive(oneb) : B(q) > B(x) /\ Con(alpha, oneb) \cap Lrns(q) # {}
      BY DEF Fresh
    <3>xcase. x = oneb \/ x \in TranClosure(known \cup {p})  BY <1>tranoneb
    <3>caseA. CASE x = oneb  BY <3>caseA
    <3>caseB. CASE x \in TranClosure(known \cup {p})
      <4>xcase2. x = p \/ x \in TranClosure(known \cup TranExclusive(p))  BY <3>caseB, <1>tc3
      <4>caseBp. CASE x = p  BY <4>caseBp, <3>Vonebp
      <4>caseBo. CASE x \in TranClosure(known \cup TranExclusive(p))
        <5>xm. x \in TranClosure(m)  BY <4>caseBo, <1>tc1, <1>knownsub, <1>tepsub
        <5>xbal. B(x) < bal  BY <4>caseBo, <1>oldballs
        <5>empty. CASE Con(alpha, oneb) \cap Lrns(x) = {}  BY <5>empty
        <5>nonempty. CASE Con(alpha, oneb) \cap Lrns(x) # {}
          <6> PICK beta \in Con(alpha, oneb) \cap Lrns(x) : TRUE  BY <5>nonempty
          <6>betaS. beta \in ConFromCaught(alpha, CaughtS(TranClosure(m)))  BY <3>S
          <6>betaLrns. beta \in Lrns(x)  OBVIOUS
          <6>xb. TopLearnerMsg(m,beta) \in TranClosure(m)
                 /\ beta \in Lrns(TopLearnerMsg(m,beta))
                 /\ B(x) <= B(TopLearnerMsg(m,beta))
            <7>ex. \E y \in TranClosure(m) : beta \in Lrns(y)  BY <5>xm, <6>betaLrns
            <7> QED BY <7>ex, <5>xm, <6>betaLrns, <1>mi, <1>balnat, <1>bound, TopLearnerMsgCorrect
          <6>bxbeta. B(x) <= BXBeta(m,beta)  BY <6>xb DEF BXBeta
          <6>bxbetastar. BXBeta(m,beta) <= BXBeta(m,bs)
            <7>ex2. \E y \in TranClosure(m) : beta \in Lrns(y)  BY <5>xm, <6>betaLrns
            <7> QED BY <3>bsMaxraw2, <6>betaS, <7>ex2
          <6>xmsg. x \in Messages  BY <5>xm, <1>mi, TranClosureClosed
          <6>bxnat. B(x) \in Ballots  BY <6>xmsg, <1>mi, BBallot
          <6>bxbmsg. TopLearnerMsg(m,beta) \in Messages  BY <6>xb, <1>mi, TranClosureClosed
          <6>bxbnat. BXBeta(m,beta) \in Ballots  BY <6>bxbmsg, <1>mi, BBallot DEF BXBeta
          <6>bxbsmsg. TopLearnerMsg(m,bs) \in TranClosure(m)  BY <3>xbmsgs2
          <6>bxbsmsg2. TopLearnerMsg(m,bs) \in Messages  BY <6>bxbsmsg, <1>mi, TranClosureClosed
          <6>bxbsnat. BXBeta(m,bs) \in Ballots  BY <6>bxbsmsg2, <1>mi, BBallot DEF BXBeta
          <6>ineq. B(x) <= BXBeta(m,bs)
            BY <6>bxbeta, <6>bxbetastar, <6>bxnat, <6>bxbnat, <6>bxbsnat DEF Ballots
          <6>caseTie. CASE B(x) = BXBeta(m,bs)
            <7>eq1. B(x) = B(TopLearnerMsg(m,bs))  BY <6>caseTie DEF BXBeta
            <7>samebal. V(x) = V(TopLearnerMsg(m,bs))  BY <7>eq1 DEF V
            <7> QED BY <7>samebal, <3>Voneb
          <6>caseStrict. CASE B(x) < BXBeta(m,bs)
            <7>bq. B(x) < B(TopLearnerMsg(m,bs))  BY <6>caseStrict DEF BXBeta
            <7>lrnsx. Con(alpha, oneb) \cap Lrns(TopLearnerMsg(m,bs)) # {}
              <8>1. bs \in Con(alpha, oneb)  BY <3>S, <3>bsIn
              <8>2. bs \in Lrns(TopLearnerMsg(m,bs))  BY <3>bsLrns2
              <8> QED BY <8>1, <8>2
            <7> QED BY <3>xbetastarInOneb, <7>bq, <7>lrnsx
          <6> QED BY <6>ineq, <6>caseTie, <6>caseStrict
        <5> QED BY <5>empty, <5>nonempty
      <4> QED BY <4>xcase2, <4>caseBp, <4>caseBo
    <3> QED BY <3>xcase, <3>caseA, <3>caseB
  <2>caseE. CASE SS = {}
    <3>capempty. S \cap RelevantLearners(m) = {}  BY <2>caseE
    <3>capemptyraw. ConFromCaught(alpha, CaughtS(TranClosure(m))) \cap RelevantLearners(m) = {}
      BY <3>capempty
    <3>Vonebp. V(oneb) = V(p)  BY <1>Boneb, <1>bpbtarg DEF V
    <3>S. Con(alpha, oneb) = ConFromCaught(alpha, CaughtS(TranClosure(m)))  BY <1>caughtoneb DEF Con
    <3> SUFFICES ASSUME NEW x \in Tran(oneb)
                 PROVE \/ V(x) = V(oneb)
                       \/ Con(alpha, oneb) \cap Lrns(x) = {}
                       \/ \E q \in TranExclusive(oneb) : B(q) > B(x) /\ Con(alpha, oneb) \cap Lrns(q) # {}
      BY DEF Fresh
    <3>xcase. x = oneb \/ x \in TranClosure(known \cup {p})  BY <1>tranoneb
    <3>caseA. CASE x = oneb  BY <3>caseA
    <3>caseB. CASE x \in TranClosure(known \cup {p})
      <4>xcase2. x = p \/ x \in TranClosure(known \cup TranExclusive(p))  BY <3>caseB, <1>tc3
      <4>caseBp. CASE x = p  BY <4>caseBp, <3>Vonebp
      <4>caseBo. CASE x \in TranClosure(known \cup TranExclusive(p))
        <5>xm. x \in TranClosure(m)  BY <4>caseBo, <1>tc1, <1>knownsub, <1>tepsub
        <5>empty. Con(alpha, oneb) \cap Lrns(x) = {}
          <6> SUFFICES ASSUME NEW beta \in Con(alpha, oneb) \cap Lrns(x) PROVE FALSE  OBVIOUS
          <6>betaS. beta \in ConFromCaught(alpha, CaughtS(TranClosure(m)))  BY <3>S
          <6>betaLearner. beta \in Learners  BY DEF Lrns
          <6>betaex. \E y \in TranClosure(m) : beta \in Lrns(y)  BY <5>xm
          <6>betaRel. beta \in RelevantLearners(m)  BY <6>betaLearner, <6>betaex DEF RelevantLearners
          <6> QED BY <6>betaS, <6>betaRel, <3>capemptyraw
        <5> QED BY <5>empty
      <4> QED BY <4>xcase2, <4>caseBp, <4>caseBo
    <3> QED BY <3>xcase, <3>caseA, <3>caseB
  <2> QED BY <2>caseNE, <2>caseE
<1> QED BY <1>Boneb, <1>isoneb, <1>fresh

LEMMA DecideableProposalOneBExists ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions,
         NEW alpha \in Learners, NEW bal \in Ballots, NEW m \in SUBSET Messages,
         alpha \in ConFromCaught(alpha, CaughtS(TranClosure(m))),
         \A x \in TranClosure(m) : B(x) < bal,
         NEW p \in Proposals,
         TranExclusive(p) = DecideableProposalTranExclusive(m),
         B(p) > bal,
         Sig(p) \notin Acceptors,
         V(p) = DecideableProposalV(alpha, bal, m)
  PROVE \A a \in Acceptors :
          \A known \in SUBSET TranClosure(m) :
          (/\ IsFiniteSet(known)
           /\ a \notin CaughtS(TranClosure(known \cup TranExclusive(p)))
          ) =>
            \E oneb \in Messages :
            (/\ Sig(oneb) = a
             /\ a \notin Caught(oneb)
             /\ IsOneB(oneb)
             /\ TranExclusive(oneb) = TranClosure(known \cup {p})
             /\ Fresh(alpha, oneb)
            )
<1>mi. TypeOKMessageInterface /\ TranTrans /\ TranFinite /\ AlwaysAProposal  BY DEF MessageInterfaceAssumptions
<1>balnat. bal \in Nat  BY DEF Ballots
<1>bound. \A x \in TranClosure(m) : B(x) < bal  OBVIOUS
<1> DEFINE S == ConFromCaught(alpha, CaughtS(TranClosure(m)))
<1> DEFINE SS == S \cap RelevantLearners(m)
<1>sL. S \subseteq Learners  BY DEF ConFromCaught
<1>tep. TranExclusive(p) = TranClosure(CQ(m))  BY DEF DecideableProposalTranExclusive
<1>cqmsgs. CQ(m) \in SUBSET Messages
  <2> SUFFICES ASSUME NEW z \in CQ(m) PROVE z \in Messages  OBVIOUS
  <2>1. z \in TranClosure(m)  BY <1>mi, <1>balnat, <1>bound, CQSubTC
  <2> QED BY <2>1, <1>mi, TranClosureClosed
<1>csub. CQ(m) \subseteq TranClosure(m)  BY <1>mi, <1>balnat, CQSubTC
<1>tesub. TranExclusive(p) \subseteq TranClosure(m)  BY <1>tep, <1>csub, <1>cqmsgs, <1>mi, TranClosureAbsorb
<1> DEFINE btarg == B(p)
<1>baltarg. bal < btarg  OBVIOUS
<1>pmsg. p \in Messages  BY <1>mi DEF TypeOKMessageInterface
<1>btbal. btarg \in Ballots  BY <1>pmsg, <1>mi, BBallot
<1>caseNE. CASE SS # {}
  <2>ssL. SS \in SUBSET Learners
    <3>1. RelevantLearners(m) \subseteq Learners  BY DEF RelevantLearners
    <3> QED BY <3>1
  <2>ssrel. \A beta \in SS : \E x \in TranClosure(m) : beta \in Lrns(x)
    <3> SUFFICES ASSUME NEW beta \in SS PROVE \E x \in TranClosure(m) : beta \in Lrns(x)  OBVIOUS
    <3>1. beta \in RelevantLearners(m)  OBVIOUS
    <3> QED BY <3>1 DEF RelevantLearners
  <2>bse. \E beta \in SS : \A gamma \in SS : BXBeta(m,gamma) <= BXBeta(m,beta)
    BY <2>ssL, <1>caseNE, <2>ssrel, <1>balnat, <1>bound, BetaStarExists
  <2> DEFINE betastar == CHOOSE beta \in SS : \A gamma \in SS : BXBeta(m,gamma) <= BXBeta(m,beta)
  <2>bsprop. betastar \in SS /\ (\A gamma \in SS : BXBeta(m,gamma) <= BXBeta(m,betastar))
    BY <2>bse
  <2>bsS. betastar \in S  BY <2>bsprop
  <2>bsSraw. betastar \in ConFromCaught(alpha, CaughtS(TranClosure(m)))  BY <2>bsS
  <2>bsRel. betastar \in RelevantLearners(m)  BY <2>bsprop
  <2>bstL. betastar \in Learners  BY <2>ssL, <2>bsprop
  <2>bsLrns. betastar \in Lrns(TopLearnerMsg(m,betastar))
    <3>ex. \E x \in TranClosure(m) : betastar \in Lrns(x)  BY <2>bsRel DEF RelevantLearners
    <3> QED BY <3>ex, <1>mi, <1>balnat, <1>bound, TopLearnerMsgCorrect
  <2>bsMax. \A beta \in S : (\E x \in TranClosure(m) : beta \in Lrns(x)) => BXBeta(m,beta) <= BXBeta(m,betastar)
    <3> SUFFICES ASSUME NEW beta \in S, \E x \in TranClosure(m) : beta \in Lrns(x)
                 PROVE BXBeta(m,beta) <= BXBeta(m,betastar)
      OBVIOUS
    <3>1. beta \in RelevantLearners(m)  BY <1>sL DEF RelevantLearners
    <3>2. beta \in SS  BY <3>1
    <3> QED BY <3>2, <2>bsprop
  <2>bsMaxraw. \A beta \in ConFromCaught(alpha, CaughtS(TranClosure(m))) :
                 (\E x \in TranClosure(m) : beta \in Lrns(x)) => BXBeta(m,beta) <= BXBeta(m,betastar)
    BY <2>bsMax
  <2>xbmsgs. TopLearnerMsg(m,betastar) \in TranClosure(m)
    <3>ex. \E x \in TranClosure(m) : betastar \in Lrns(x)  BY <2>bsRel DEF RelevantLearners
    <3> QED BY <3>ex, <1>mi, <1>balnat, <1>bound, TopLearnerMsgCorrect
  <2>dpv. DecideableProposalV(alpha,bal,m) = V(TopLearnerMsg(m,betastar))
    BY <1>caseNE DEF DecideableProposalV
  <2>vp. V(p) = V(TopLearnerMsg(m,betastar))  BY <2>dpv
  <2>exhyp. \E bal2 \in Ballots, btarg2 \in Ballots, betastar2 \in Learners :
              /\ TranExclusive(p) = TranClosure(CQ(m))
              /\ B(p) = btarg2
              /\ Sig(p) \notin Acceptors
              /\ (\A x \in TranClosure(m) : B(x) < bal2)
              /\ bal2 < btarg2
              /\ betastar2 \in ConFromCaught(alpha, CaughtS(TranClosure(m)))
              /\ TopLearnerMsg(m,betastar2) \in TranClosure(m)
              /\ betastar2 \in Lrns(TopLearnerMsg(m,betastar2))
              /\ (\A beta \in ConFromCaught(alpha, CaughtS(TranClosure(m))) :
                   (\E x \in TranClosure(m) : beta \in Lrns(x)) => BXBeta(m,beta) <= BXBeta(m,betastar2))
              /\ V(p) = V(TopLearnerMsg(m,betastar2))
    <3> WITNESS bal \in Ballots, btarg \in Ballots, betastar \in Learners
    <3> QED BY <1>tep, <1>bound, <1>baltarg, <2>bsSraw, <2>xbmsgs, <2>bsLrns, <2>bsMaxraw, <2>vp
  <2> QED BY MessageInterfaceAssumptions, LearnerGraphAssumptions, <2>exhyp, OneBFresh
<1>caseE. CASE SS = {}
  <2>capempty. S \cap RelevantLearners(m) = {}  BY <1>caseE
  <2>capemptyraw. ConFromCaught(alpha, CaughtS(TranClosure(m))) \cap RelevantLearners(m) = {}
    BY <2>capempty
  <2>exhyp. \E bal2 \in Ballots, btarg2 \in Ballots :
              /\ TranExclusive(p) = TranClosure(CQ(m))
              /\ B(p) = btarg2
              /\ Sig(p) \notin Acceptors
              /\ (\A x \in TranClosure(m) : B(x) < bal2)
              /\ bal2 < btarg2
    <3> WITNESS bal \in Ballots, btarg \in Ballots
    <3> QED BY <1>tep, <1>bound, <1>baltarg
  <2> QED BY MessageInterfaceAssumptions, LearnerGraphAssumptions, <2>exhyp, <2>capemptyraw, OneBFreshDegenerate
<1> QED BY <1>caseNE, <1>caseE

THEOREM DecideableProposalExists == 
  (/\ MessageInterfaceAssumptions
   /\ LearnerGraphAssumptions
   /\ ValueInterfaceAssumptions) =>
    \A alpha \in Learners :
    \A bal \in Ballots :
    \A m \in SUBSET Messages :
    (/\ alpha \in ConFromCaught(alpha, CaughtS(TranClosure(m)))
     /\ \A x \in TranClosure(m) : B(x) < bal
    ) => \E p \in Proposals :
         (/\ TranExclusive(p) \subseteq TranClosure(m)
          /\ B(p) > bal
          /\ \A a \in Acceptors:
             \A known \in SUBSET TranClosure(m):
             (/\ IsFiniteSet(known)
              /\ a \notin CaughtS(TranClosure(known \cup TranExclusive(p)))
             )=>
               \E oneb \in Messages :
               (/\ Sig(oneb) = a
                /\ a \notin Caught(oneb)
                /\ IsOneB(oneb)
                /\ TranExclusive(oneb) = TranClosure(known \cup {p})
                /\ Fresh(alpha, oneb)
               )
         )
<1> SUFFICES ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions, ValueInterfaceAssumptions,
                    NEW alpha \in Learners, NEW bal \in Ballots, NEW m \in SUBSET Messages,
                    alpha \in ConFromCaught(alpha, CaughtS(TranClosure(m))),
                    \A x \in TranClosure(m) : B(x) < bal
             PROVE \E p \in Proposals :
                     (/\ TranExclusive(p) \subseteq TranClosure(m)
                      /\ B(p) > bal
                      /\ \A a \in Acceptors:
                         \A known \in SUBSET TranClosure(m):
                         (/\ IsFiniteSet(known)
                          /\ a \notin CaughtS(TranClosure(known \cup TranExclusive(p)))
                         )=>
                           \E oneb \in Messages :
                           (/\ Sig(oneb) = a
                            /\ a \notin Caught(oneb)
                            /\ IsOneB(oneb)
                            /\ TranExclusive(oneb) = TranClosure(known \cup {p})
                            /\ Fresh(alpha, oneb)
                           )
                     )
  OBVIOUS
<1>mi. TypeOKMessageInterface /\ TranTrans /\ TranFinite /\ AlwaysAProposal  BY DEF MessageInterfaceAssumptions
<1>balnat. bal \in Nat  BY DEF Ballots
<1>bound. \A x \in TranClosure(m) : B(x) < bal  OBVIOUS
<1>pex. \E p \in Proposals :
          /\ TranExclusive(p) = DecideableProposalTranExclusive(m)
          /\ B(p) > bal
          /\ Sig(p) \notin Acceptors
          /\ V(p) = DecideableProposalV(alpha, bal, m)
  BY MessageInterfaceAssumptions, LearnerGraphAssumptions, ValueInterfaceAssumptions, DecideableProposalPExists
<1> PICK p \in Proposals :
      /\ TranExclusive(p) = DecideableProposalTranExclusive(m)
      /\ B(p) > bal
      /\ Sig(p) \notin Acceptors
      /\ V(p) = DecideableProposalV(alpha, bal, m)
  BY <1>pex
<1>cqmsgs. CQ(m) \in SUBSET Messages
  <2> SUFFICES ASSUME NEW z \in CQ(m) PROVE z \in Messages  OBVIOUS
  <2>1. z \in TranClosure(m)  BY <1>mi, <1>balnat, <1>bound, CQSubTC
  <2> QED BY <2>1, <1>mi, TranClosureClosed
<1>csub. CQ(m) \subseteq TranClosure(m)  BY <1>mi, <1>balnat, CQSubTC
<1>tep. TranExclusive(p) = TranClosure(CQ(m))  BY DEF DecideableProposalTranExclusive
<1>tesub. TranExclusive(p) \subseteq TranClosure(m)  BY <1>tep, <1>csub, <1>cqmsgs, <1>mi, TranClosureAbsorb
<1>ex1. \A a \in Acceptors :
          \A known \in SUBSET TranClosure(m) :
            (/\ IsFiniteSet(known) /\ a \notin CaughtS(TranClosure(known \cup TranExclusive(p))))
            => \E oneb \in Messages :
                 (/\ Sig(oneb) = a /\ a \notin Caught(oneb) /\ IsOneB(oneb)
                  /\ TranExclusive(oneb) = TranClosure(known \cup {p}) /\ Fresh(alpha, oneb))
  BY MessageInterfaceAssumptions, LearnerGraphAssumptions, DecideableProposalOneBExists
<1> QED BY <1>tesub, <1>ex1


====================================================================

