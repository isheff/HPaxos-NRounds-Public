-------------------------- MODULE NetworkSpec --------------------------
\* A PlusCal model of the message network for the honest (safe) acceptors.
\*
\*   - Network      : the set of messages that have ever been sent.  Grows only.
\*   - known_messages[s] : the messages safe acceptor s has learned.  Grows only.
\*
\* Each safe acceptor s is modeled as one process PER (s, x) PAIR it might ever
\* receive.  That process's single step does two things atomically:
\*   1. Learn message x from the Network.  This is only allowed if s already
\*      knows every message in TranExclusive(x) (its whole prior history).
\*   2. Forced send: if -- once x is learned -- there exists a message y signed
\*      by s whose exclusive transitive history TranExclusive(y) is EXACTLY the
\*      set (known_messages[s] with x added) \cup (messages already signed by s
\*      in the Network), then s MUST send y (add it to the Network).
\*
\* The forced-send set is exactly one message shape (its history is pinned down
\* to a specific set), so at most one y qualifies up to that history.
\*
\* Byzantine senders (Senders \ SafeAcceptors) ignore known_messages entirely:
\* at any time such an s may send ANY message it signs whose exclusive history
\* is already fully in the Network.  This is any non-safe sender, not just
\* non-safe acceptors -- e.g. it also covers proposers behaving adversarially.
EXTENDS MessageInterface, Naturals, TLAPS

LOCAL INSTANCE FiniteSetTheorems

CONSTANT SafeAcceptors
ASSUME SafeAcceptorsSubsetAcceptors == SafeAcceptors \subseteq Acceptors

\* Live acceptors are safe acceptors whose step is required (weakly fairly) to
\* eventually happen when continuously enabled -- see NetworkAssumption below.
CONSTANT LiveAcceptors
ASSUME LiveAcceptorsSubsetSafeAcceptors == LiveAcceptors \subseteq SafeAcceptors

ByzantineAcceptors == Senders \ SafeAcceptors

(* --algorithm HPaxosNet {
     variables
       Network = {},
       known_messages = [s \in SafeAcceptors |-> {}];

     \* One process per (safe acceptor, message) PAIR: whenever that message's
     \* whole prior history is already known to that acceptor, learn it (and
     \* forced-send).  Indexing by the pair -- rather than one process per
     \* acceptor with an internal `with` over the message -- means weak fairness
     \* can be imposed directly on each (acceptor, message) process (see
     \* NetworkAssumption), with no separate operator needed to relate the
     \* fairness action to the system's step relation.
     process (acc_msg \in SafeAcceptors \times Messages)
     {
       lstep:
         while (TRUE) {
           LET ACC == acc_msg[1]
               MSG == acc_msg[2]
           IN  when /\ MSG \in Network
                    /\ TranExclusive(MSG) \subseteq known_messages[ACC];
               known_messages[ACC] := known_messages[ACC] \cup {MSG};
               \* Forced send: if a message signed by ACC with history exactly
               \* (known_messages[ACC] with MSG, plus ACC's own
               \* sent messages) exists, one such message MUST be sent (taken
               \* deterministically -- it is unique up to its history).
               Network := LET T == (known_messages[ACC] \cup {MSG})
                                   \cup {m \in Network : Sig(m) = ACC}
                              M == {y \in (Messages \ Proposals) :
                                    Sig(y) = ACC /\ TranExclusive(y) = T}
                          IN IF M # {}
                            THEN Network \cup {CHOOSE y \in M}
                            ELSE Network;
         }
     }

     process (byz \in (Senders \ SafeAcceptors))
     {
       bstep:
         while (TRUE) {
           \* A Byzantine acceptor may send any message it signs whose entire
           \* prior history is already in the Network.  It never consults
           \* known_messages.
           with (y \in {z \in Messages : Sig(z) = self /\ TranExclusive(z) \subseteq Network}) {
             Network := Network \cup {y};
           }
         }
     }
   }
*)
\* BEGIN TRANSLATION
VARIABLES Network, known_messages

vars == << Network, known_messages >>

ProcSet == (SafeAcceptors \times Messages) \cup (ByzantineAcceptors)

Init == (* Global variables *)
        /\ Network = {}
        /\ known_messages = [s \in SafeAcceptors |-> {}]

safe_acceptor_receives_message(self) ==
  /\ self[2] \in Network
  /\ TranExclusive(self[2]) \subseteq known_messages[self[1]]
  /\ known_messages' = [known_messages EXCEPT ![self[1]] = known_messages[self[1]] \cup {self[2]}]
  /\ Network' = (LET T == (known_messages'[self[1]] \cup {self[2]})
                          \cup {m \in Network : Sig(m) = self[1]} IN
                 IF \E y \in (Messages \ Proposals) : Sig(y) = self[1] /\ TranExclusive(y) = T
                   THEN Network \cup {CHOOSE y \in (Messages \ Proposals) :
                                        Sig(y) = self[1] /\ TranExclusive(y) = T}
                   ELSE Network)

byz(self) == /\ \E y \in {z \in Messages : Sig(z) = self /\ TranExclusive(z) \subseteq Network}:
                  Network' = (Network \cup {y})
             /\ UNCHANGED known_messages

Next == (\E self \in SafeAcceptors \times Messages: safe_acceptor_receives_message(self))
           \/ (\E self \in ByzantineAcceptors: byz(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

\* ===================================================================
\* Per-message fairness
\* ===================================================================
\* Each live acceptor's learn step for each individual message is weakly fair:
\* if learning a particular x stays continuously enabled, it must eventually
\* happen.  Weak fairness on safe_acceptor_receives_message(self) as a whole
\* (a `fair process` annotation, self ranging only over acceptors) would only
\* force SOME learn step of each acceptor, not the learn of a PARTICULAR
\* message -- a live acceptor could be starved of one x forever while it keeps
\* learning others.  Imposing WF per (acceptor, message) pair, restricted to
\* LiveAcceptors, is exactly what we need.
NetworkAssumption == \A self \in LiveAcceptors \times Messages : WF_vars(safe_acceptor_receives_message(self))

\* Backends cannot instantiate a \A-bound WF_vars(...) fact at a literal tuple
\* constructor (e.g. WF_vars(F(<<a, x>>))) via a bare `DEF NetworkAssumption`
\* citation -- congruence through WF_vars doesn't fire on syntactically-built
\* tuples, only on an already-bound pair variable.  This lemma does the
\* instantiation once, at a bound `self`, so call sites can get their literal-
\* tuple instance via ordinary lemma application (which unifies fine) instead.
LEMMA NetworkAssumptionInst ==
  ASSUME NEW self \in LiveAcceptors \times Messages, NetworkAssumption
  PROVE  WF_vars(safe_acceptor_receives_message(self))
BY DEF NetworkAssumption

SafeAcceptorsUncaughtInvariant ==
  SafeAcceptors \cap CaughtS(Network) = {}

DecisionStableInvariant ==
  \A alpha \in Learners :
  \A bal \in Ballots :
  Decision(Network, alpha, bal) => []Decision(Network, alpha, bal)

AgreementInvariant == 
  \A alpha \in Learners :
  \A beta  \in Learners :
  \A alphabal \in Ballots :
  \A betabal  \in Ballots :
  (/\ SafeAcceptors \in SafetySets({alpha, beta})
   /\ Decision(Network, alpha, alphabal) 
   /\ Decision(Network, beta,  betabal ) 
  ) => BalToVal(alphabal) = BalToVal(betabal)

OneBInvariant ==
  \A s \in SafeAcceptors :
  \A b \in Ballots :
  \A p \in known_messages[s] :
  (/\ B(p) = b
   /\ IsProposal(p)
   /\ \A x \in known_messages[s] : IsProposal(x) => B(x) <= b
  ) => \E oneb \in Network :
  (/\ B(oneb) = b
   /\ Sig(oneb) = s
   /\ IsOneB(oneb)
  )

TwoAInvariant ==
  \A s \in SafeAcceptors :
  \A b \in Ballots :
  \A alpha \in Learners:
  \A d \in (1..(MaxDepth(alpha))):
  (/\ SafeAcceptors \in SafetySets({alpha})
   /\ (\A x \in known_messages[s] : (IsProposal(x) => B(x) <= b))
   /\ SigS({x \in known_messages[s] :
           B(x) = b /\ HasDepth(alpha, x, d-1)}) \in Quorums(alpha)
  ) => \E twoa \in Network :
  (/\ B(twoa) = b
   /\ Sig(twoa) = s
   /\ HasDepth(alpha, twoa, d)
   /\ IsTwoA(twoa))
  

\* ===================================================================
\* Inductive invariant
\* ===================================================================
Inv ==
  /\ Network \in SUBSET Messages
  /\ known_messages \in [SafeAcceptors -> SUBSET Messages]
  /\ IsFiniteSet(Network)
  /\ \A s \in SafeAcceptors : known_messages[s] \subseteq Network
  /\ \A z \in Network : TranExclusive(z) \subseteq Network

LEMMA InitInv == Init => Inv
<1> SUFFICES ASSUME Init PROVE Inv  OBVIOUS
<1>1. Network = {} /\ known_messages = [s \in SafeAcceptors |-> {}]  BY DEF Init
<1>2. IsFiniteSet(Network)  BY <1>1, FS_EmptySet
<1> QED  BY <1>1, <1>2 DEF Inv

LEMMA InvStep == Inv /\ [Next]_vars => Inv'
<1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'  OBVIOUS
<1>i. /\ Network \in SUBSET Messages
      /\ known_messages \in [SafeAcceptors -> SUBSET Messages]
      /\ IsFiniteSet(Network)
      /\ (\A s \in SafeAcceptors : known_messages[s] \subseteq Network)
      /\ (\A z \in Network : TranExclusive(z) \subseteq Network)
  BY DEF Inv
<1>2. CASE vars' = vars
  BY <1>2, <1>i DEF Inv, vars
<1>3. CASE \E self \in SafeAcceptors \times Messages : safe_acceptor_receives_message(self)
  <2>1. PICK p \in SafeAcceptors \times Messages : safe_acceptor_receives_message(p)  BY <1>3
  <2> DEFINE self == p[1]
  <2> DEFINE x == p[2]
  <2>2. /\ x \in Network
        /\ TranExclusive(x) \subseteq known_messages[self]
        /\ known_messages' = [known_messages EXCEPT ![self] = known_messages[self] \cup {x}]
        /\ Network' = (LET T == (known_messages'[self] \cup {x})
                                  \cup {m \in Network : Sig(m) = self} IN
                       IF \E y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T
                         THEN Network \cup {CHOOSE y \in (Messages \ Proposals) :
                                             Sig(y) = self /\ TranExclusive(y) = T}
                         ELSE Network)
     BY <2>1 DEF safe_acceptor_receives_message
  <2>1a. self \in SafeAcceptors  BY <2>1
  <2>x. x \in Network /\ TranExclusive(x) \subseteq known_messages[self]  BY <2>2
  <2>k. known_messages' = [known_messages EXCEPT ![self] = known_messages[self] \cup {x}]  BY <2>2
  <2>kself. known_messages'[self] = known_messages[self] \cup {x}  BY <2>k, <1>i, <2>1a
  <2> DEFINE T == (known_messages'[self] \cup {x}) \cup {m \in Network : Sig(m) = self}
  <2>tsub. T \subseteq Network
    <3>1. known_messages[self] \subseteq Network  BY <1>i, <2>1a
    <3>2. known_messages'[self] \subseteq Network  BY <2>kself, <3>1, <2>x
    <3>3. {m \in Network : Sig(m) = self} \subseteq Network  OBVIOUS
    <3> QED  BY <3>2, <3>3, <2>x
  <2>net. Network' = (IF \E y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T
                        THEN Network \cup {CHOOSE y \in (Messages \ Proposals) :
                                            Sig(y) = self /\ TranExclusive(y) = T}
                        ELSE Network)
     BY <2>2
  <2>ndisj. \/ Network' = Network
            \/ \E y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T /\ Network' = Network \cup {y}
    <3>1. CASE \E y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T
      <4> DEFINE y0 == CHOOSE y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T
      <4>1. y0 \in (Messages \ Proposals) /\ Sig(y0) = self /\ TranExclusive(y0) = T  BY <3>1
      <4>2. Network' = Network \cup {y0}  BY <2>net, <3>1
      <4> QED  BY <4>1, <4>2
    <3>2. CASE ~(\E y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T)
      BY <2>net, <3>2
    <3> QED  BY <3>1, <3>2
  <2>kp. known_messages' \in [SafeAcceptors -> SUBSET Messages]
         /\ (\A s \in SafeAcceptors : known_messages'[s] \subseteq Network')
    <3>net. Network \subseteq Network'  BY <2>ndisj
    <3>1. known_messages[self] \cup {x} \subseteq Messages  BY <1>i, <2>x, <2>1a
    <3>2. known_messages' \in [SafeAcceptors -> SUBSET Messages]  BY <2>k, <3>1, <1>i, <2>1a
    <3>3. ASSUME NEW s \in SafeAcceptors PROVE known_messages'[s] \subseteq Network'
      <4>1. CASE s = self  BY <4>1, <2>kself, <1>i, <2>x, <3>net
      <4>2. CASE s # self  BY <4>2, <2>k, <1>i, <3>net
      <4> QED  BY <4>1, <4>2
    <3> QED  BY <3>2, <3>3
  <2>np. Network' \in SUBSET Messages /\ IsFiniteSet(Network')
         /\ (\A z \in Network' : TranExclusive(z) \subseteq Network')
    <3>1. CASE Network' = Network
      BY <3>1, <1>i
    <3>2. CASE \E y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T /\ Network' = Network \cup {y}
      <4> PICK y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T /\ Network' = Network \cup {y}
        BY <3>2
      <4>1. Network' \in SUBSET Messages  BY <1>i
      <4>2. IsFiniteSet(Network')  BY <1>i, FS_AddElement
      <4>3. ASSUME NEW z \in Network' PROVE TranExclusive(z) \subseteq Network'
        <5>1. CASE z \in Network  BY <5>1, <1>i
        <5>2. CASE z = y  BY <5>2, <2>tsub
        <5> QED  BY <5>1, <5>2
      <4> QED  BY <4>1, <4>2, <4>3
    <3> QED  BY <2>ndisj, <3>1, <3>2
  <2> QED  BY <2>kp, <2>np DEF Inv
<1>4. CASE \E self \in ByzantineAcceptors : byz(self)
  <2>1. PICK self \in ByzantineAcceptors : byz(self)  BY <1>4
  <2>2. PICK y \in {z \in Messages : Sig(z) = self /\ TranExclusive(z) \subseteq Network} :
              Network' = (Network \cup {y})
     BY <2>1 DEF byz
  <2>k. known_messages' = known_messages  BY <2>1 DEF byz
  <2>y. y \in Messages /\ TranExclusive(y) \subseteq Network  BY <2>2
  <2>np. Network' \in SUBSET Messages /\ IsFiniteSet(Network')
         /\ (\A z \in Network' : TranExclusive(z) \subseteq Network')
    <3>1. Network' \in SUBSET Messages  BY <2>2, <2>y, <1>i
    <3>2. IsFiniteSet(Network')  BY <2>2, <1>i, FS_AddElement
    <3>3. ASSUME NEW z \in Network' PROVE TranExclusive(z) \subseteq Network'
      <4>1. CASE z \in Network  BY <4>1, <1>i, <2>2
      <4>2. CASE z = y  BY <4>2, <2>y, <2>2
      <4> QED  BY <4>1, <4>2, <2>2
    <3> QED  BY <3>1, <3>2, <3>3
  <2>kp. known_messages' \in [SafeAcceptors -> SUBSET Messages]
         /\ (\A s \in SafeAcceptors : known_messages'[s] \subseteq Network')
    <3>net. Network \subseteq Network'  BY <2>2
    <3> QED  BY <2>k, <1>i, <3>net
  <2> QED  BY <2>kp, <2>np DEF Inv
<1> QED  BY <1>2, <1>3, <1>4 DEF Next

LEMMA InvHolds == Spec => []Inv
<1>1. Init => Inv  BY InitInv
<1>2. Inv /\ [Next]_vars => Inv'  BY InvStep
<1> QED  BY <1>1, <1>2, PTL DEF Spec

\* ===================================================================
\* Liveness: monotonicity, stability, leads-to combinators
\* ===================================================================

\* ENABLED of the per-message learn action (deterministic send => trivial).
LEMMA LearnEnabled ==
  ASSUME NEW a \in SafeAcceptors, NEW x \in Network,
         TranExclusive(x) \subseteq known_messages[a],
         x \notin known_messages[a],
         known_messages \in [SafeAcceptors -> SUBSET Messages]
  PROVE  ENABLED <<safe_acceptor_receives_message(<<a, x>>)>>_vars
BY ExpandENABLED DEF safe_acceptor_receives_message, vars

\* Network and each known_messages[s] only grow.
LEMMA NetMono == [Next]_vars => Network \subseteq Network'
<1>1. CASE vars' = vars  BY <1>1 DEF vars
<1>2. CASE \E self \in SafeAcceptors \times Messages : safe_acceptor_receives_message(self)
  <2> PICK self \in SafeAcceptors \times Messages : safe_acceptor_receives_message(self)  BY <1>2
  <2> QED  BY DEF safe_acceptor_receives_message
<1>3. CASE \E self \in ByzantineAcceptors : byz(self)
  <2> PICK self \in ByzantineAcceptors : byz(self)  BY <1>3
  <2> QED  BY DEF byz
<1> QED  BY <1>1, <1>2, <1>3 DEF Next

LEMMA KnownMono ==
  Inv /\ [Next]_vars => \A s \in SafeAcceptors : known_messages[s] \subseteq known_messages'[s]
<1> SUFFICES ASSUME Inv, [Next]_vars, NEW s \in SafeAcceptors
             PROVE known_messages[s] \subseteq known_messages'[s]  OBVIOUS
<1>i. known_messages \in [SafeAcceptors -> SUBSET Messages]  BY DEF Inv
<1>1. CASE vars' = vars  BY <1>1 DEF vars
<1>2. CASE \E self \in SafeAcceptors \times Messages : safe_acceptor_receives_message(self)
  <2> PICK self \in SafeAcceptors \times Messages : safe_acceptor_receives_message(self)  BY <1>2
  <2>2. known_messages' = [known_messages EXCEPT ![self[1]] = known_messages[self[1]] \cup {self[2]}]
    BY DEF safe_acceptor_receives_message
  <2>3. CASE s = self[1]  BY <2>3, <2>2, <1>i
  <2>4. CASE s # self[1]  BY <2>4, <2>2, <1>i
  <2> QED  BY <2>3, <2>4
<1>3. CASE \E self \in ByzantineAcceptors : byz(self)
  <2> PICK self \in ByzantineAcceptors : byz(self)  BY <1>3
  <2> QED  BY DEF byz
<1> QED  BY <1>1, <1>2, <1>3 DEF Next

\* Stability: once true, stays true (Network and known only grow).
LEMMA NetStable ==
  ASSUME NEW xx
  PROVE  Spec => [](xx \in Network => [](xx \in Network))
<1>1. xx \in Network /\ [Next]_vars => (xx \in Network)'  BY NetMono
<1> QED  BY <1>1, PTL DEF Spec

LEMMA SubsetNetworkStable ==
  ASSUME NEW SS
  PROVE  Spec => [](SS \subseteq Network => [](SS \subseteq Network))
<1>1. SS \subseteq Network /\ [Next]_vars => (SS \subseteq Network)'  BY NetMono
<1> QED  BY <1>1, PTL DEF Spec

LEMMA KnownStable ==
  ASSUME NEW a \in SafeAcceptors, NEW w
  PROVE  Spec => [](w \in known_messages[a] => [](w \in known_messages[a]))
<1>1. Inv /\ [Next]_vars /\ w \in known_messages[a] => (w \in known_messages[a])'  BY KnownMono
<1>2. Spec => []Inv  BY InvHolds
<1> QED  BY <1>1, <1>2, PTL DEF Spec

LEMMA SubsetKnownStable ==
  ASSUME NEW a \in SafeAcceptors, NEW SS
  PROVE  Spec => [](SS \subseteq known_messages[a] => [](SS \subseteq known_messages[a]))
<1>1. Inv /\ [Next]_vars /\ SS \subseteq known_messages[a] => (SS \subseteq known_messages[a])'  BY KnownMono
<1>2. Spec => []Inv  BY InvHolds
<1> QED  BY <1>1, <1>2, PTL DEF Spec

\* Pure-PTL leads-to combinators.
LEMMA StableConj ==
  ASSUME TEMPORAL AA, TEMPORAL BB, TEMPORAL CC,
         AA ~> BB, AA ~> CC, [](BB => []BB), [](CC => []CC)
  PROVE  AA ~> (BB /\ CC)
BY PTL

LEMMA StablePair ==
  ASSUME TEMPORAL BB, TEMPORAL CC, [](BB => []BB), [](CC => []CC)
  PROVE  [](BB /\ CC => [](BB /\ CC))
BY PTL

LEMMA LtTrans ==
  ASSUME TEMPORAL F, TEMPORAL G, TEMPORAL H, F ~> G, G ~> H
  PROVE  F ~> H
BY PTL

LEMMA LtStrengthen ==
  ASSUME TEMPORAL F, TEMPORAL G, TEMPORAL H, [](F => G), G ~> H
  PROVE  F ~> H
BY PTL

\* Single-message learn leads-to (WF1, boxed-premise recipe).
LEMMA LearnLeadsTo ==
  ASSUME NEW a \in LiveAcceptors, NEW x \in Messages
  PROVE  Spec /\ NetworkAssumption =>
           ((x \in Network /\ TranExclusive(x) \subseteq known_messages[a])
             ~> (x \in known_messages[a]))
<1>a. a \in SafeAcceptors  BY LiveAcceptorsSubsetSafeAcceptors
<1> DEFINE P == Inv /\ x \in Network /\ TranExclusive(x) \subseteq known_messages[a]
                    /\ x \notin known_messages[a]
<1> DEFINE Q == x \in known_messages[a]
<1> DEFINE R == x \in Network /\ TranExclusive(x) \subseteq known_messages[a]
<1>inv. Spec => []Inv  BY InvHolds
<1>b1. Spec => [](P /\ [Next]_vars => (P' \/ Q'))
  <2>1. P /\ [Next]_vars => (P' \/ Q')
    <3>1. Inv /\ [Next]_vars => Inv'  BY InvStep
    <3>2. [Next]_vars => Network \subseteq Network'  BY NetMono
    <3>3. Inv /\ [Next]_vars => known_messages[a] \subseteq known_messages'[a]  BY KnownMono, <1>a
    <3> QED  BY <3>1, <3>2, <3>3
  <2> QED  BY <2>1, PTL DEF Spec
<1>b2. Spec => [](P /\ <<Next /\ safe_acceptor_receives_message(<<a, x>>)>>_vars => Q')
  <2>1. P /\ <<Next /\ safe_acceptor_receives_message(<<a, x>>)>>_vars => Q'
    BY <1>a DEF safe_acceptor_receives_message, Inv
  <2> QED  BY <2>1, PTL DEF Spec
<1>b3. Spec => [](P => ENABLED <<safe_acceptor_receives_message(<<a, x>>)>>_vars)
  <2>1. P => ENABLED <<safe_acceptor_receives_message(<<a, x>>)>>_vars  BY <1>a, LearnEnabled DEF Inv
  <2> QED  BY <2>1, PTL DEF Spec
<1>axmem. <<a, x>> \in LiveAcceptors \times Messages  OBVIOUS
<1>w. Spec /\ NetworkAssumption => WF_vars(safe_acceptor_receives_message(<<a, x>>))
  <2>1. NetworkAssumption => WF_vars(safe_acceptor_receives_message(<<a, x>>))
    BY <1>axmem, NetworkAssumptionInst
  <2> QED  BY <2>1
<1>n. Spec => [][Next]_vars  BY DEF Spec
<1>pq. Spec /\ NetworkAssumption => (P ~> Q)  BY <1>b1, <1>b2, <1>b3, <1>w, <1>n, PTL
<1>ri. Spec => [](R => (P \/ Q))
  <2>1. Inv /\ R => (P \/ Q)  OBVIOUS
  <2>2. Spec => [](Inv /\ R => (P \/ Q))  BY <2>1, PTL DEF Spec
  <2> QED  BY <2>2, <1>inv, PTL
<1> QED  BY <1>pq, <1>ri, PTL

\* ===================================================================
\* Finite conjunction of leads-to (combinator).  Top-level (hideable)
\* operators so that \A-over-temporal ELIMINATION is FO over opaque symbols
\* (plain \A-elim of a temporal body is unsupported by every TLAPS backend).
\* The leads-to SOURCE is (Src \subseteq Network) for a set parameter Src --
\* NOT a temporal parameter -- because temporal parameters cannot be
\* instantiated when the lemma is applied.
\* ===================================================================
CP_Tgt(U)       == \A p \in U : p[2] \in known_messages[p[1]]
CP_LT(Src, p)   == (Spec /\ NetworkAssumption)
                     => ((Src \subseteq Network) ~> (p[2] \in known_messages[p[1]]))
CP_Good(Src, U) == /\ ((Spec /\ NetworkAssumption) => ((Src \subseteq Network) ~> CP_Tgt(U)))
                   /\ (Spec => [](CP_Tgt(U) => []CP_Tgt(U)))
CP_Hyp(Src, U)  == /\ IsFiniteSet(U) /\ U \subseteq SafeAcceptors \X Messages
                   /\ \A p \in U : CP_LT(Src, p)
CPLop(Src, SS)  == (Spec /\ NetworkAssumption) => ((Src \subseteq Network) ~> CP_Tgt(SS))

\* Clean-context helpers for the fragile INV1-style boxing (PTL chokes on the
\* heavy context inside ConjPairLeadsTo's induction).
LEMMA BoxTgtEmpty == ASSUME NEW U, U = {} PROVE Spec => [](CP_Tgt(U))
<1>1. Init => CP_Tgt(U)  BY DEF CP_Tgt
<1>2. CP_Tgt(U) /\ [Next]_vars => (CP_Tgt(U))'  BY DEF CP_Tgt
<1> QED  BY <1>1, <1>2, PTL DEF Spec

LEMMA BoxTgtSplit ==
  ASSUME NEW U, NEW p0, p0 \in U
  PROVE  Spec => [](CP_Tgt(U) <=> (CP_Tgt(U \ {p0}) /\ p0[2] \in known_messages[p0[1]]))
<1>1. Init => (CP_Tgt(U) <=> (CP_Tgt(U \ {p0}) /\ p0[2] \in known_messages[p0[1]]))
  BY DEF CP_Tgt
<1>2. (CP_Tgt(U) <=> (CP_Tgt(U \ {p0}) /\ p0[2] \in known_messages[p0[1]])) /\ [Next]_vars
        => (CP_Tgt(U) <=> (CP_Tgt(U \ {p0}) /\ p0[2] \in known_messages[p0[1]]))'
  BY DEF CP_Tgt
<1> QED  BY <1>1, <1>2, PTL DEF Spec

LEMMA KnownStablePair ==
  ASSUME NEW p0 \in SafeAcceptors \X Messages
  PROVE  Spec => [](p0[2] \in known_messages[p0[1]] => [](p0[2] \in known_messages[p0[1]]))
<1>1. p0[1] \in SafeAcceptors  OBVIOUS
<1>2. Inv /\ [Next]_vars /\ p0[2] \in known_messages[p0[1]]
        => (p0[2] \in known_messages[p0[1]])'
  BY KnownMono, <1>1
<1>3. Spec => []Inv  BY InvHolds
<1> QED  BY <1>2, <1>3, PTL DEF Spec

LEMMA ConjPairLeadsTo ==
  ASSUME NEW SS, NEW Src, CP_Hyp(Src, SS)
  PROVE  CPLop(Src, SS)
<1> DEFINE Q(n) == \A U : (CP_Hyp(Src, U) /\ Cardinality(U) = n) => CP_Good(Src, U)
<1> HIDE DEF CP_LT, CP_Good, CP_Hyp
<1>all. \A n \in Nat : Q(n)
  <2> HIDE DEF Q
  <2>ind. \A n \in Nat : (\A k \in 0..(n-1) : Q(k)) => Q(n)
    <3> SUFFICES ASSUME NEW n \in Nat, \A k \in 0..(n-1) : Q(k),
                        NEW U, CP_Hyp(Src, U), Cardinality(U) = n
                 PROVE CP_Good(Src, U)
      BY DEF Q
    <3>hyp. /\ IsFiniteSet(U) /\ U \subseteq SafeAcceptors \X Messages
            /\ \A p \in U : CP_LT(Src, p)
      BY DEF CP_Hyp
    <3>1. CASE U = {}
      <4>box. Spec => [](CP_Tgt(U))  BY <3>1, BoxTgtEmpty
      <4>2. (Spec /\ NetworkAssumption) => ((Src \subseteq Network) ~> CP_Tgt(U))
        BY <4>box, PTL
      <4>3. Spec => [](CP_Tgt(U) => []CP_Tgt(U))  BY <4>box, PTL
      <4> QED  BY <4>2, <4>3 DEF CP_Good
    <3>2. CASE U # {}
      <4>0. PICK p0 \in U : TRUE  BY <3>2
      <4> DEFINE U0 == U \ {p0}
      <4>card. Cardinality(U) >= 1  BY <3>hyp, FS_EmptySet, FS_CardinalityType
      <4>n1. n - 1 \in Nat  BY <4>card
      <4>U0f. IsFiniteSet(U0) /\ Cardinality(U0) = n - 1  BY <3>hyp, <4>0, FS_RemoveElement
      <4>U0h. CP_Hyp(Src, U0)
        <5>1. \A p \in U0 : CP_LT(Src, p)  BY <3>hyp
        <5> QED  BY <4>U0f, <3>hyp, <5>1 DEF CP_Hyp
      <4>gU0. CP_Good(Src, U0)
        <5>k. n - 1 \in 0..(n-1)  BY <4>n1
        <5>q. Q(n - 1)  BY <5>k
        <5>a. (CP_Hyp(Src, U0) /\ Cardinality(U0) = n - 1) => CP_Good(Src, U0)
          BY <5>q DEF Q
        <5> QED  BY <5>a, <4>U0h, <4>U0f
      <4>lt0. (Spec /\ NetworkAssumption) => ((Src \subseteq Network) ~> CP_Tgt(U0))
        BY <4>gU0 DEF CP_Good
      <4>st0. Spec => [](CP_Tgt(U0) => []CP_Tgt(U0))  BY <4>gU0 DEF CP_Good
      <4>p0m. p0[1] \in SafeAcceptors /\ p0[2] \in Messages  BY <4>0, <3>hyp
      <4>p0lt0. \A p \in U : CP_LT(Src, p)  BY <3>hyp
      <4>p0lt. (Spec /\ NetworkAssumption)
                 => ((Src \subseteq Network) ~> (p0[2] \in known_messages[p0[1]]))
        <5>1. CP_LT(Src, p0)  BY <4>p0lt0, <4>0
        <5> QED  BY <5>1 DEF CP_LT
      <4>p0pair. p0 \in SafeAcceptors \X Messages  BY <4>0, <3>hyp
      <4>p0st. Spec => [](p0[2] \in known_messages[p0[1]]
                          => [](p0[2] \in known_messages[p0[1]]))
        BY <4>p0pair, KnownStablePair
      <4>boxsplit. Spec => [](CP_Tgt(U) <=> (CP_Tgt(U0) /\ p0[2] \in known_messages[p0[1]]))
        BY <4>0, BoxTgtSplit
      <4>ltU. (Spec /\ NetworkAssumption) => ((Src \subseteq Network) ~> CP_Tgt(U))
        <5>1. (Spec /\ NetworkAssumption)
                => ((Src \subseteq Network) ~> (CP_Tgt(U0) /\ p0[2] \in known_messages[p0[1]]))
          BY <4>lt0, <4>p0lt, <4>st0, <4>p0st, PTL
        <5> QED  BY <5>1, <4>boxsplit, PTL
      <4>stU. Spec => [](CP_Tgt(U) => []CP_Tgt(U))
        <5>1. Spec => [](CP_Tgt(U0) /\ p0[2] \in known_messages[p0[1]]
                         => [](CP_Tgt(U0) /\ p0[2] \in known_messages[p0[1]]))
          BY <4>st0, <4>p0st, PTL
        <5> QED  BY <5>1, <4>boxsplit, PTL
      <4> QED  BY <4>ltU, <4>stU DEF CP_Good
    <3> QED  BY <3>1, <3>2
  <2> QED  BY <2>ind, GeneralNatInduction, IsaM("blast")
<1>cn. Cardinality(SS) \in Nat  BY FS_CardinalityType DEF CP_Hyp
<1>qss. Q(Cardinality(SS))
  <2> HIDE DEF Q
  <2> QED  BY <1>all, <1>cn
<1>gss. CP_Good(Src, SS)
  <2>a. (CP_Hyp(Src, SS) /\ Cardinality(SS) = Cardinality(SS)) => CP_Good(Src, SS)
    BY <1>qss DEF Q
  <2> QED  BY <2>a
<1> QED  BY <1>gss DEF CP_Good, CPLop

\* ===================================================================
\* KnowLeadsTo: x in Network ~> x in known_messages[a]  (Tran-depth induction)
\* Op-wrapped conclusions: temporal-conclusion lemmas can only be APPLIED with
\* identity/non-temporal parameters; wrapping the conclusion in a top-level op
\* makes the instantiation first-order over the opaque symbol.
\* ===================================================================
KLT(a, xx)  == (Spec /\ NetworkAssumption) => ((xx \in Network) ~> (xx \in known_messages[a]))
SKSop(a, S) == Spec => [](S \subseteq known_messages[a] => [](S \subseteq known_messages[a]))
LLTop(a, xx) == (Spec /\ NetworkAssumption)
                  => ((xx \in Network /\ TranExclusive(xx) \subseteq known_messages[a])
                       ~> (xx \in known_messages[a]))
BTCop(xx, w) == Spec => [](({xx} \subseteq Network) => w \in Network)
BTPop(a, T)  == Spec => [](CP_Tgt({a} \X T) <=> (T \subseteq known_messages[a]))
NBop(xx)     == Spec => [](({xx} \subseteq Network) <=> (xx \in Network))
BKEop(p, a)  == Spec => [](p[2] \in known_messages[p[1]] <=> p[2] \in known_messages[a])

\* Product-set equivalence (explicit tuple reasoning; SMT/auto fail on it).
LEMMA ProdEq ==
  ASSUME NEW a, NEW T, NEW kn
  PROVE  (\A p \in {a} \X T : p[2] \in kn[p[1]]) <=> (T \subseteq kn[a])
<1>1. ASSUME \A p \in {a} \X T : p[2] \in kn[p[1]], NEW w \in T PROVE w \in kn[a]
  <2>1. <<a, w>> \in {a} \X T  BY <1>1
  <2>2. <<a, w>>[2] \in kn[<<a, w>>[1]]  BY <1>1, <2>1
  <2> QED  BY <2>2
<1>2. ASSUME T \subseteq kn[a], NEW p \in {a} \X T PROVE p[2] \in kn[p[1]]
  <2>1. p[1] = a /\ p[2] \in T  BY <1>2
  <2> QED  BY <2>1, <1>2
<1> QED  BY <1>1, <1>2

LEMMA BoxTranClosed ==
  ASSUME NEW xx \in Messages, NEW w, w \in TranExclusive(xx)
  PROVE  BTCop(xx, w)
<1> USE DEF BTCop
<1>1. Inv /\ {xx} \subseteq Network => w \in Network  BY DEF Inv
<1>2. Spec => []Inv  BY InvHolds
<1> QED  BY <1>1, <1>2, PTL DEF Spec

LEMMA NetBridge == ASSUME NEW xx PROVE NBop(xx)
<1> USE DEF NBop
<1>1. Init => (({xx} \subseteq Network) <=> (xx \in Network))  OBVIOUS
<1>2. (({xx} \subseteq Network) <=> (xx \in Network)) /\ [Next]_vars
        => (({xx} \subseteq Network) <=> (xx \in Network))'  OBVIOUS
<1> QED  BY <1>1, <1>2, PTL DEF Spec

LEMMA BoxKnownEq == ASSUME NEW p, NEW a, p[1] = a PROVE BKEop(p, a)
<1> USE DEF BKEop
<1>1. Init => (p[2] \in known_messages[p[1]] <=> p[2] \in known_messages[a])  OBVIOUS
<1>2. (p[2] \in known_messages[p[1]] <=> p[2] \in known_messages[a]) /\ [Next]_vars
        => (p[2] \in known_messages[p[1]] <=> p[2] \in known_messages[a])'  OBVIOUS
<1> QED  BY <1>1, <1>2, PTL DEF Spec

LEMMA BoxTgtProduct ==
  ASSUME NEW a, NEW T
  PROVE  BTPop(a, T)
<1> USE DEF BTPop
<1>1. Init => (CP_Tgt({a} \X T) <=> (T \subseteq known_messages[a]))
  BY ProdEq DEF CP_Tgt
<1>2. (CP_Tgt({a} \X T) <=> (T \subseteq known_messages[a])) /\ [Next]_vars
        => (CP_Tgt({a} \X T) <=> (T \subseteq known_messages[a]))'
  BY ProdEq DEF CP_Tgt
<1> QED  BY <1>1, <1>2, PTL DEF Spec

\* Thin op-wrappers over the (already proven) temporal lemmas (identity citation).
LEMMA SubsetKnownStableW == ASSUME NEW a \in SafeAcceptors, NEW SS PROVE SKSop(a, SS)
BY SubsetKnownStable DEF SKSop
LEMMA LearnLeadsToW == ASSUME NEW a \in LiveAcceptors, NEW x \in Messages PROVE LLTop(a, x)
BY LearnLeadsTo DEF LLTop

LEMMA KnowLeadsTo ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions,
         NEW a \in LiveAcceptors, NEW x \in Messages
  PROVE  (Spec /\ NetworkAssumption) => ((x \in Network) ~> (x \in known_messages[a]))
<1>aS. a \in SafeAcceptors  BY LiveAcceptorsSubsetSafeAcceptors
<1>mi. TranFinite /\ TranTrans /\ TranAcyclic /\ TypeOKMessageInterface
  BY DEF MessageInterfaceAssumptions
<1> DEFINE Q(n) == \A xx \in Messages : Cardinality(Tran(xx)) = n => KLT(a, xx)
<1> HIDE DEF KLT
<1>all. \A n \in Nat : Q(n)
  <2> HIDE DEF Q
  <2>ind. \A n \in Nat : (\A k \in 0..(n-1) : Q(k)) => Q(n)
    <3> SUFFICES ASSUME NEW n \in Nat, \A k \in 0..(n-1) : Q(k),
                        NEW xx \in Messages, Cardinality(Tran(xx)) = n
                 PROVE KLT(a, xx)
      BY DEF Q
    <3>tesub. TranExclusive(xx) \subseteq Messages
      BY <1>mi, TranSubMessages DEF TranExclusive
    <3>xtf. IsFiniteSet(Tran(xx))  BY <1>mi DEF TranFinite
    <3>tef. IsFiniteSet(TranExclusive(xx))  BY <3>xtf, FS_Subset DEF TranExclusive
    <3>ssf. IsFiniteSet({a} \X TranExclusive(xx))  BY <3>tef, FS_Singleton, FS_Product
    <3>sssub. {a} \X TranExclusive(xx) \subseteq SafeAcceptors \X Messages  BY <1>aS, <3>tesub
    <3>plt. \A p \in {a} \X TranExclusive(xx) : CP_LT({xx}, p)
      <4> SUFFICES ASSUME NEW p \in {a} \X TranExclusive(xx)
                   PROVE CP_LT({xx}, p)  OBVIOUS
      <4>pd. p[1] = a /\ p[2] \in TranExclusive(xx)  OBVIOUS
      <4>wm. p[2] \in Messages  BY <4>pd, <3>tesub
      <4>wcard. Cardinality(Tran(p[2])) < n  BY <4>pd, <1>mi, TranExclusiveDecreasesTranSize
      <4>wnat. Cardinality(Tran(p[2])) \in Nat  BY <4>wm, <1>mi, FS_CardinalityType DEF TranFinite
      <4>klw. KLT(a, p[2])
        <5>1. Cardinality(Tran(p[2])) \in 0..(n-1)  BY <4>wcard, <4>wnat
        <5>2. Q(Cardinality(Tran(p[2])))
          <6> HIDE DEF Q
          <6> QED  BY <5>1
        <5> QED  BY <5>2, <4>wm DEF Q
      <4>wl. (Spec /\ NetworkAssumption) => ((p[2] \in Network) ~> (p[2] \in known_messages[a]))
        BY <4>klw DEF KLT
      <4>box. Spec => [](({xx} \subseteq Network) => p[2] \in Network)
        <5>1. BTCop(xx, p[2])  BY <4>pd, <4>wm, BoxTranClosed
        <5> QED  BY <5>1 DEF BTCop
      <4>ltxw. (Spec /\ NetworkAssumption) => (({xx} \subseteq Network) ~> (p[2] \in known_messages[a]))
        BY <4>wl, <4>box, PTL
      <4>bke. Spec => [](p[2] \in known_messages[p[1]] <=> p[2] \in known_messages[a])
        <5>1. BKEop(p, a)  BY <4>pd, BoxKnownEq
        <5> QED  BY <5>1 DEF BKEop
      <4> QED  BY <4>ltxw, <4>bke, PTL DEF CP_LT
    <3>hyp. CP_Hyp({xx}, {a} \X TranExclusive(xx))
      BY <3>ssf, <3>sssub, <3>plt DEF CP_Hyp
    <3>conj. CPLop({xx}, {a} \X TranExclusive(xx))
      BY <3>hyp, ConjPairLeadsTo
    <3>conj0. (Spec /\ NetworkAssumption)
                => (({xx} \subseteq Network) ~> CP_Tgt({a} \X TranExclusive(xx)))
      BY <3>conj DEF CPLop
    <3>nb. Spec => [](({xx} \subseteq Network) <=> (xx \in Network))
      <4>1. NBop(xx)  BY NetBridge
      <4> QED  BY <4>1 DEF NBop
    <3>conj1. (Spec /\ NetworkAssumption)
                => ((xx \in Network) ~> CP_Tgt({a} \X TranExclusive(xx)))
      BY <3>conj0, <3>nb, PTL
    <3>tgtbox. Spec => [](CP_Tgt({a} \X TranExclusive(xx))
                          <=> (TranExclusive(xx) \subseteq known_messages[a]))
      <4>1. BTPop(a, TranExclusive(xx))  BY BoxTgtProduct
      <4> QED  BY <4>1 DEF BTPop
    <3>conj2. (Spec /\ NetworkAssumption)
                => ((xx \in Network) ~> (TranExclusive(xx) \subseteq known_messages[a]))
      BY <3>conj1, <3>tgtbox, PTL
    <3>learn. (Spec /\ NetworkAssumption)
                => ((xx \in Network /\ TranExclusive(xx) \subseteq known_messages[a])
                     ~> (xx \in known_messages[a]))
      <4>1. LLTop(a, xx)  BY LearnLeadsToW
      <4> QED  BY <4>1 DEF LLTop
    <3>netst. Spec => [](xx \in Network => [](xx \in Network))  BY NetStable
    <3>test. Spec => [](TranExclusive(xx) \subseteq known_messages[a]
                        => [](TranExclusive(xx) \subseteq known_messages[a]))
      <4>1. SKSop(a, TranExclusive(xx))  BY <1>aS, SubsetKnownStableW
      <4> QED  BY <4>1 DEF SKSop
    <3>conj3. (Spec /\ NetworkAssumption)
                => ((xx \in Network)
                     ~> (xx \in Network /\ TranExclusive(xx) \subseteq known_messages[a]))
      BY <3>conj2, <3>netst, <3>test, PTL
    <3>kxx. (Spec /\ NetworkAssumption) => ((xx \in Network) ~> (xx \in known_messages[a]))
      BY <3>conj3, <3>learn, PTL
    <3> QED  BY <3>kxx DEF KLT
  <2> QED  BY <2>ind, GeneralNatInduction, IsaM("blast")
<1>cn. Cardinality(Tran(x)) \in Nat  BY <1>mi, FS_CardinalityType DEF TranFinite
<1>qx. Q(Cardinality(Tran(x)))
  <2> HIDE DEF Q
  <2> QED  BY <1>all, <1>cn
<1>kx. KLT(a, x)  BY <1>qx DEF Q
<1> QED  BY <1>kx DEF KLT

\* ===================================================================
\* EventuallyKnown: m \subseteq Network ~> every live acceptor knows all of m
\* ===================================================================
BMNop(m, x)  == Spec => [](m \subseteq Network => x \in Network)
ELtgt(m)     == \A a \in LiveAcceptors : m \subseteq known_messages[a]
BTLop(m)     == Spec => [](CP_Tgt(LiveAcceptors \X m) <=> ELtgt(m))

LEMMA KnowLeadsToW ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions,
         NEW a \in LiveAcceptors, NEW x \in Messages
  PROVE  KLT(a, x)
BY KnowLeadsTo DEF KLT

LEMMA BoxMemInNet == ASSUME NEW m, NEW x, x \in m PROVE BMNop(m, x)
<1> USE DEF BMNop
<1>1. Init => (m \subseteq Network => x \in Network)  OBVIOUS
<1>2. (m \subseteq Network => x \in Network) /\ [Next]_vars
        => (m \subseteq Network => x \in Network)'  OBVIOUS
<1> QED  BY <1>1, <1>2, PTL DEF Spec

LEMMA ProdCurry ==
  ASSUME NEW AA, NEW BB, NEW kn
  PROVE  (\A p \in AA \X BB : p[2] \in kn[p[1]]) <=> (\A aa \in AA : BB \subseteq kn[aa])
<1>1. ASSUME \A p \in AA \X BB : p[2] \in kn[p[1]], NEW aa \in AA, NEW x \in BB
      PROVE x \in kn[aa]
  <2>1. <<aa, x>> \in AA \X BB  BY <1>1
  <2>2. <<aa, x>>[2] \in kn[<<aa, x>>[1]]  BY <1>1, <2>1
  <2> QED  BY <2>2
<1>2. ASSUME \A aa \in AA : BB \subseteq kn[aa], NEW p \in AA \X BB PROVE p[2] \in kn[p[1]]
  <2>1. p[1] \in AA /\ p[2] \in BB  BY <1>2
  <2> QED  BY <2>1, <1>2
<1> QED  BY <1>1, <1>2

LEMMA BoxTgtLive == ASSUME NEW m PROVE BTLop(m)
<1> USE DEF BTLop
<1>1. Init => (CP_Tgt(LiveAcceptors \X m) <=> ELtgt(m))
  BY ProdCurry DEF CP_Tgt, ELtgt
<1>2. (CP_Tgt(LiveAcceptors \X m) <=> ELtgt(m)) /\ [Next]_vars
      => (CP_Tgt(LiveAcceptors \X m) <=> ELtgt(m))'
  BY ProdCurry DEF CP_Tgt, ELtgt
<1> QED  BY <1>1, <1>2, PTL DEF Spec

LEMMA NetFiniteAlways == Spec => [](IsFiniteSet(Network))
<1>1. Spec => []Inv  BY InvHolds
<1> QED  BY <1>1, PTL DEF Inv

LEMMA BoxFinImpNotSub ==
  ASSUME NEW m, ~IsFiniteSet(m)
  PROVE  Spec => [](IsFiniteSet(Network) => ~(m \subseteq Network))
<1>1. Init => (IsFiniteSet(Network) => ~(m \subseteq Network))  BY FS_Subset
<1>2. (IsFiniteSet(Network) => ~(m \subseteq Network)) /\ [Next]_vars
        => (IsFiniteSet(Network) => ~(m \subseteq Network))'  BY FS_Subset
<1> QED  BY <1>1, <1>2, PTL DEF Spec

\* EventuallyKnown: once a set of messages is all in the Network, every live
\* acceptor eventually knows all of it.  We do NOT assume m is finite: whenever
\* m \subseteq Network holds, Network is finite (it starts empty and grows by at
\* most one per step), so m is finite there (infinite m: vacuous, since m can
\* never be a subset of the always-finite Network).
THEOREM EventuallyKnown ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions
  PROVE  Spec /\ NetworkAssumption =>
           \A m \in SUBSET Messages :
             (m \subseteq Network) ~>
             (\A a \in LiveAcceptors : m \subseteq known_messages[a])
<1>fa. IsFiniteSet(Acceptors)  BY DEF LearnerGraphAssumptions, FiniteAcceptors
<1>lsub. LiveAcceptors \subseteq Acceptors
  BY LiveAcceptorsSubsetSafeAcceptors, SafeAcceptorsSubsetAcceptors
<1>lfin. IsFiniteSet(LiveAcceptors)  BY <1>fa, <1>lsub, FS_Subset
<1> SUFFICES ASSUME NEW m \in SUBSET Messages
             PROVE  Spec /\ NetworkAssumption =>
                      ((m \subseteq Network) ~> (\A a \in LiveAcceptors : m \subseteq known_messages[a]))
  OBVIOUS
<1>fin. CASE IsFiniteSet(m)
  <2>ssf. IsFiniteSet(LiveAcceptors \X m)  BY <1>lfin, <1>fin, FS_Product
  <2>sssub. LiveAcceptors \X m \subseteq SafeAcceptors \X Messages
    BY LiveAcceptorsSubsetSafeAcceptors
  <2>plt. \A p \in LiveAcceptors \X m : CP_LT(m, p)
    <3> SUFFICES ASSUME NEW p \in LiveAcceptors \X m PROVE CP_LT(m, p)  OBVIOUS
    <3>pd. p[1] \in LiveAcceptors /\ p[2] \in m  OBVIOUS
    <3>pm. p[2] \in Messages  BY <3>pd
    <3>kl. KLT(p[1], p[2])  BY <3>pd, <3>pm, KnowLeadsToW
    <3>klu. (Spec /\ NetworkAssumption) => ((p[2] \in Network) ~> (p[2] \in known_messages[p[1]]))
      BY <3>kl DEF KLT
    <3>box. Spec => [](m \subseteq Network => p[2] \in Network)
      <4>1. BMNop(m, p[2])  BY <3>pd, BoxMemInNet
      <4> QED  BY <4>1 DEF BMNop
    <3> QED  BY <3>klu, <3>box, PTL DEF CP_LT
  <2>hyp. CP_Hyp(m, LiveAcceptors \X m)  BY <2>ssf, <2>sssub, <2>plt DEF CP_Hyp
  <2>conj. CPLop(m, LiveAcceptors \X m)  BY <2>hyp, ConjPairLeadsTo
  <2>conj0. (Spec /\ NetworkAssumption)
              => ((m \subseteq Network) ~> CP_Tgt(LiveAcceptors \X m))
    BY <2>conj DEF CPLop
  <2>tb. Spec => [](CP_Tgt(LiveAcceptors \X m) <=> ELtgt(m))
    <3>1. BTLop(m)  BY BoxTgtLive
    <3> QED  BY <3>1 DEF BTLop
  <2>et. (Spec /\ NetworkAssumption) => ((m \subseteq Network) ~> ELtgt(m))
    BY <2>conj0, <2>tb, PTL
  <2> QED  BY <2>et DEF ELtgt
<1>inf. CASE ~IsFiniteSet(m)
  <2>fin2. Spec => [](IsFiniteSet(Network))  BY NetFiniteAlways
  <2>imp. Spec => [](IsFiniteSet(Network) => ~(m \subseteq Network))  BY <1>inf, BoxFinImpNotSub
  <2>ns. Spec => [](~(m \subseteq Network))  BY <2>fin2, <2>imp, PTL
  <2> QED  BY <2>ns, PTL
<1> QED  BY <1>fin, <1>inf

\* I don't think we need this generalization. 
\* THEOREM EventuallySentEventuallyKnown ==
\*   (/\ MessageInterfaceAssumptions
\*    /\ LearnerGraphAssumptions
\*    /\ Spec
\*    /\ NetworkAssumption) =>
\*       \A m \in SUBSET Messages :
\*         (IsFiniteSet(m) /\ (\A x \in m : (<>(x \in Network)))) =>
\*         (<>([](\A a \in LiveAcceptors : m \subseteq known_messages[a])))

LEMMA TranClosureMono ==
  ASSUME NEW m \in SUBSET Messages, NEW mp \in SUBSET Messages, m \subseteq mp
  PROVE TranClosure(m) \subseteq TranClosure(mp)
<1> SUFFICES ASSUME NEW z \in TranClosure(m) PROVE z \in TranClosure(mp)  OBVIOUS
<1>1. PICK x \in m : z \in Tran(x)  BY DEF TranClosure
<1>2. x \in mp  BY <1>1
<1> QED BY <1>1, <1>2 DEF TranClosure

\* Decision == DecisionSlow only (DecisionFast was dropped from Decision
\* upstream in MessageInterface.tla), so monotonicity only needs the
\* DecisionSlow / quorum-upward-closure argument.
LEMMA DecisionMono ==
  ASSUME LearnerGraphAssumptions,
         NEW m \in SUBSET Messages, NEW mp \in SUBSET Messages, m \subseteq mp,
         NEW alpha \in Learners, NEW bal \in Ballots,
         Decision(m, alpha, bal)
  PROVE Decision(mp, alpha, bal)
<1>fa. FiniteAcceptors  BY DEF LearnerGraphAssumptions
<1>tcm. TranClosure(m) \subseteq TranClosure(mp)  BY TranClosureMono
<1>slow. DecisionSlow(m,alpha,bal)  BY DEF Decision
<1> DEFINE W == {x \in TranClosure(m) : B(x) = bal /\ HasDepth(alpha, x, MaxDepth(alpha))}
<1> DEFINE Wp == {x \in TranClosure(mp) : B(x) = bal /\ HasDepth(alpha, x, MaxDepth(alpha))}
<1>quo. SigS(W) \in Quorums(alpha)  BY <1>slow DEF DecisionSlow
<1>sub. W \subseteq Wp  BY <1>tcm
<1>sigsub. SigS(W) \subseteq SigS(Wp)  BY <1>sub DEF SigS
<1>acc. SigS(Wp) \subseteq Acceptors
  <2> SUFFICES ASSUME NEW aa \in SigS(Wp) PROVE aa \in Acceptors  OBVIOUS
  <2>1. PICK y \in Wp : aa = Sig(y)  BY DEF SigS
  <2>2. HasDepth(alpha, y, MaxDepth(alpha))  BY <2>1
  <2> QED BY <2>2, <2>1 DEF HasDepth
<1>finacc. IsFiniteSet(Acceptors)  BY <1>fa DEF FiniteAcceptors
<1>fin. IsFiniteSet(SigS(Wp))  BY <1>acc, <1>finacc, FS_Subset
<1>up. SigS(Wp) \in Quorums(alpha)  BY <1>quo, <1>sigsub, <1>acc, <1>fin, QuorumUpward
<1> QED BY <1>up DEF DecisionSlow, Decision

LEMMA DecisionOneStep ==
  ASSUME LearnerGraphAssumptions,
         NEW alpha \in Learners, NEW bal \in Ballots
  PROVE Inv /\ [Next]_vars /\ Decision(Network, alpha, bal) => Decision(Network, alpha, bal)'
<1> SUFFICES ASSUME Inv, [Next]_vars, Decision(Network, alpha, bal)
             PROVE Decision(Network, alpha, bal)'
  OBVIOUS
<1>netsub. Network \in SUBSET Messages  BY DEF Inv
<1>net. Network \subseteq Network'  BY NetMono
<1>invp. Inv'  BY InvStep
<1>netsub2. Network' \in SUBSET Messages  BY <1>invp DEF Inv
<1>dm. Decision(Network', alpha, bal)  BY <1>netsub, <1>netsub2, <1>net, DecisionMono
<1> QED BY <1>dm

LEMMA DecisionStableFixed ==
  ASSUME LearnerGraphAssumptions,
         NEW alpha \in Learners, NEW bal \in Ballots
  PROVE Spec => [](Decision(Network, alpha, bal) => [](Decision(Network, alpha, bal)))
<1>1. Inv /\ [Next]_vars /\ Decision(Network,alpha,bal) => Decision(Network,alpha,bal)'  BY DecisionOneStep
<1>2. Spec => []Inv  BY InvHolds
<1> QED BY <1>1, <1>2, PTL DEF Spec

LEMMA AlwaysDecisionStableInvariant ==
  (/\ Spec
   /\ MessageInterfaceAssumptions
   /\ ValueInterfaceAssumptions
   /\ LearnerGraphAssumptions
  )=> []DecisionStableInvariant
<1> SUFFICES ASSUME Spec, MessageInterfaceAssumptions, ValueInterfaceAssumptions, LearnerGraphAssumptions
             PROVE []DecisionStableInvariant
  OBVIOUS
<1>fixed. \A alpha \in Learners : \A bal \in Ballots :
            [](Decision(Network, alpha, bal) => [](Decision(Network, alpha, bal)))
  BY DecisionStableFixed
<1> QED BY <1>fixed DEF DecisionStableInvariant

SafeAcceptorChainInv ==
  \A s \in SafeAcceptors : \A m1, m2 \in Network :
    (Sig(m1) = s /\ Sig(m2) = s) => (m1 \in Tran(m2) \/ m2 \in Tran(m1))

LEMMA InitChain == Init => SafeAcceptorChainInv
<1> SUFFICES ASSUME Init PROVE SafeAcceptorChainInv  OBVIOUS
<1>1. Network = {}  BY DEF Init
<1> QED BY <1>1 DEF SafeAcceptorChainInv

LEMMA ChainStep ==
  Inv /\ SafeAcceptorChainInv /\ [Next]_vars => SafeAcceptorChainInv'
<1> SUFFICES ASSUME Inv, SafeAcceptorChainInv, [Next]_vars PROVE SafeAcceptorChainInv'  OBVIOUS
<1>i. /\ Network \in SUBSET Messages
      /\ known_messages \in [SafeAcceptors -> SUBSET Messages]
      /\ IsFiniteSet(Network)
      /\ (\A s \in SafeAcceptors : known_messages[s] \subseteq Network)
      /\ (\A z \in Network : TranExclusive(z) \subseteq Network)
  BY DEF Inv
<1>2. CASE vars' = vars
  BY <1>2 DEF SafeAcceptorChainInv, vars
<1>3. CASE \E self \in SafeAcceptors \times Messages : safe_acceptor_receives_message(self)
  <2>1. PICK p \in SafeAcceptors \times Messages : safe_acceptor_receives_message(p)  BY <1>3
  <2> DEFINE self == p[1]
  <2> DEFINE x == p[2]
  <2>2. /\ x \in Network
        /\ TranExclusive(x) \subseteq known_messages[self]
        /\ known_messages' = [known_messages EXCEPT ![self] = known_messages[self] \cup {x}]
        /\ Network' = (LET T == (known_messages'[self] \cup {x})
                                  \cup {m \in Network : Sig(m) = self} IN
                       IF \E y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T
                         THEN Network \cup {CHOOSE y \in (Messages \ Proposals) :
                                             Sig(y) = self /\ TranExclusive(y) = T}
                         ELSE Network)
     BY <2>1 DEF safe_acceptor_receives_message
  <2>1a. self \in SafeAcceptors  BY <2>1
  <2>x. x \in Network /\ TranExclusive(x) \subseteq known_messages[self]  BY <2>2
  <2>k. known_messages' = [known_messages EXCEPT ![self] = known_messages[self] \cup {x}]  BY <2>2
  <2>kself. known_messages'[self] = known_messages[self] \cup {x}  BY <2>k, <1>i, <2>1a
  <2> DEFINE T == (known_messages'[self] \cup {x}) \cup {m \in Network : Sig(m) = self}
  <2>net. Network' = (IF \E y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T
                        THEN Network \cup {CHOOSE y \in (Messages \ Proposals) :
                                            Sig(y) = self /\ TranExclusive(y) = T}
                        ELSE Network)
     BY <2>2
  <2>ndisj. \/ Network' = Network
            \/ \E y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T /\ Network' = Network \cup {y}
    <3>1. CASE \E y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T
      <4> DEFINE y0 == CHOOSE y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T
      <4>1. y0 \in (Messages \ Proposals) /\ Sig(y0) = self /\ TranExclusive(y0) = T  BY <3>1
      <4>2. Network' = Network \cup {y0}  BY <2>net, <3>1
      <4> QED  BY <4>1, <4>2
    <3>2. CASE ~(\E y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T)
      BY <2>net, <3>2
    <3> QED  BY <3>1, <3>2
  <2>a. CASE Network' = Network
    BY <2>a DEF SafeAcceptorChainInv
  <2>b. CASE \E y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T /\ Network' = Network \cup {y}
    <3> PICK y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T /\ Network' = Network \cup {y}
       BY <2>b
    <3>tsub2. {m \in Network : Sig(m) = self} \subseteq TranExclusive(y)  OBVIOUS
    <3>suf. SUFFICES ASSUME NEW s \in SafeAcceptors, NEW m1 \in Network', NEW m2 \in Network',
                        Sig(m1) = s, Sig(m2) = s
                 PROVE m1 \in Tran(m2) \/ m2 \in Tran(m1)
      BY DEF SafeAcceptorChainInv
    <3>m1. m1 \in Network \/ m1 = y  BY <3>suf
    <3>m2. m2 \in Network \/ m2 = y  BY <3>suf
    <3>case11. CASE m1 \in Network /\ m2 \in Network
      BY <3>case11, <3>suf DEF SafeAcceptorChainInv
    <3>case1y. CASE m1 \in Network /\ m2 = y
      <4>1. m1 \in {m \in Network : Sig(m) = self}  BY <3>case1y, <3>suf
      <4>2. m1 \in TranExclusive(y)  BY <4>1, <3>tsub2
      <4>3. m1 \in Tran(y)  BY <4>2 DEF TranExclusive
      <4> QED  BY <4>3, <3>case1y
    <3>casey1. CASE m1 = y /\ m2 \in Network
      <4>1. m2 \in {m \in Network : Sig(m) = self}  BY <3>casey1, <3>suf
      <4>2. m2 \in TranExclusive(y)  BY <4>1, <3>tsub2
      <4>3. m2 \in Tran(y)  BY <4>2 DEF TranExclusive
      <4> QED  BY <4>3, <3>casey1
    <3>caseyy. CASE m1 = y /\ m2 = y
      <4>1. m1 \in Tran(m1)  BY DEF Tran
      <4> QED  BY <4>1, <3>caseyy
    <3> QED BY <3>case11, <3>case1y, <3>casey1, <3>caseyy, <3>m1, <3>m2
  <2> QED BY <2>ndisj, <2>a, <2>b
<1>4. CASE \E self \in ByzantineAcceptors : byz(self)
  <2>1. PICK self \in ByzantineAcceptors : byz(self)  BY <1>4
  <2>2. PICK y \in {z \in Messages : Sig(z) = self /\ TranExclusive(z) \subseteq Network} :
              Network' = (Network \cup {y})
     BY <2>1 DEF byz
  <2>selfnotsafe. self \notin SafeAcceptors  BY <2>1 DEF ByzantineAcceptors
  <2> SUFFICES ASSUME NEW s \in SafeAcceptors, NEW m1 \in Network', NEW m2 \in Network',
                      Sig(m1) = s, Sig(m2) = s
               PROVE m1 \in Tran(m2) \/ m2 \in Tran(m1)
    BY DEF SafeAcceptorChainInv
  <2>m1. m1 \in Network \/ m1 = y  BY <2>2
  <2>m2. m2 \in Network \/ m2 = y  BY <2>2
  <2>m1net. m1 \in Network
    <3> SUFFICES ASSUME m1 = y PROVE FALSE  BY <2>m1
    <3> QED BY <2>selfnotsafe
  <2>m2net. m2 \in Network
    <3> SUFFICES ASSUME m2 = y PROVE FALSE  BY <2>m2
    <3> QED BY <2>selfnotsafe
  <2> QED BY <2>m1net, <2>m2net DEF SafeAcceptorChainInv
<1> QED BY <1>2, <1>3, <1>4 DEF Next

LEMMA ChainHolds == Spec => []SafeAcceptorChainInv
<1>1. Init => SafeAcceptorChainInv  BY InitChain
<1>2. Inv /\ SafeAcceptorChainInv /\ [Next]_vars => SafeAcceptorChainInv'  BY ChainStep
<1>3. Spec => []Inv  BY InvHolds
<1> QED BY <1>1, <1>2, <1>3, PTL DEF Spec

LEMMA ChainImpliesUncaught ==
  SafeAcceptorChainInv => SafeAcceptorsUncaughtInvariant
<1> SUFFICES ASSUME SafeAcceptorChainInv
             PROVE SafeAcceptorsUncaughtInvariant
  OBVIOUS
<1> SUFFICES ASSUME SafeAcceptors \cap CaughtS(Network) # {} PROVE FALSE
  BY DEF SafeAcceptorsUncaughtInvariant
<1>1. PICK s \in SafeAcceptors \cap CaughtS(Network) : TRUE  OBVIOUS
<1>2. s \in SafeAcceptors /\ s \in CaughtS(Network)  BY <1>1
<1>3. \E m1 \in Network : \E m2 \in Network :
        Sig(m1) = s /\ Sig(m2) = s /\ m1 \notin Tran(m2) /\ m2 \notin Tran(m1)
  BY <1>2 DEF CaughtS
<1>4. PICK m1 \in Network : \E m2 \in Network :
        Sig(m1) = s /\ Sig(m2) = s /\ m1 \notin Tran(m2) /\ m2 \notin Tran(m1)
  BY <1>3
<1>5. PICK m2 \in Network :
        Sig(m1) = s /\ Sig(m2) = s /\ m1 \notin Tran(m2) /\ m2 \notin Tran(m1)
  BY <1>4
<1>comp. m1 \in Tran(m2) \/ m2 \in Tran(m1)  BY <1>2, <1>5 DEF SafeAcceptorChainInv
<1> QED BY <1>comp, <1>5

LEMMA AlwaysSafeAcceptorsUncaughtInvariant ==
  (/\ Spec
   /\ MessageInterfaceAssumptions
   /\ ValueInterfaceAssumptions
   /\ LearnerGraphAssumptions
  )=> []SafeAcceptorsUncaughtInvariant
<1> SUFFICES ASSUME Spec, MessageInterfaceAssumptions, ValueInterfaceAssumptions, LearnerGraphAssumptions
             PROVE []SafeAcceptorsUncaughtInvariant
  OBVIOUS
<1>chain. Spec => []SafeAcceptorChainInv  BY ChainHolds
<1> QED BY <1>chain, ChainImpliesUncaught, PTL

LEMMA NetworkTranClosureEq ==
  ASSUME Inv
  PROVE TranClosure(Network) = Network
<1>sub1. Network \subseteq TranClosure(Network)
  BY DEF TranClosure, Tran
<1>sub2. TranClosure(Network) \subseteq Network
  <2> SUFFICES ASSUME NEW z \in TranClosure(Network) PROVE z \in Network
    BY DEF TranClosure
  <2>1. PICK y \in Network : z \in Tran(y)  BY DEF TranClosure
  <2>2. z = y \/ z \in TranExclusive(y)  BY <2>1 DEF Tran, TranExclusive
  <2>3. TranExclusive(y) \subseteq Network  BY <2>1 DEF Inv
  <2> QED BY <2>1, <2>2, <2>3
<1> QED BY <1>sub1, <1>sub2

LEMMA AgreementFromSafeUncaught ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions, ValueInterfaceAssumptions,
         Inv, SafeAcceptorsUncaughtInvariant
  PROVE AgreementInvariant
<1> SUFFICES ASSUME NEW alpha \in Learners, NEW beta \in Learners,
                    NEW alphabal \in Ballots, NEW betabal \in Ballots,
                    SafeAcceptors \in SafetySets({alpha, beta}),
                    Decision(Network, alpha, alphabal),
                    Decision(Network, beta, betabal)
             PROVE BalToVal(alphabal) = BalToVal(betabal)
  BY DEF AgreementInvariant
<1>tc. TranClosure(Network) = Network  BY NetworkTranClosureEq
<1>unc. SafeAcceptors \cap CaughtS(Network) = {}  BY DEF SafeAcceptorsUncaughtInvariant
<1>con. alpha \in ConFromCaught(beta, CaughtS(TranClosure(Network)))
  BY <1>tc, <1>unc DEF ConFromCaught
<1>netsub. Network \in SUBSET Messages  BY DEF Inv
<1> QED BY <1>con, <1>netsub, AgreementM

THEOREM AlwaysAgreementInvariant ==
  (/\ Spec
   /\ MessageInterfaceAssumptions
   /\ ValueInterfaceAssumptions
   /\ LearnerGraphAssumptions
  )=> []AgreementInvariant
<1> SUFFICES ASSUME Spec, MessageInterfaceAssumptions, ValueInterfaceAssumptions, LearnerGraphAssumptions
             PROVE []AgreementInvariant
  OBVIOUS
<1>1. []Inv  BY InvHolds
<1>2. []SafeAcceptorsUncaughtInvariant  BY AlwaysSafeAcceptorsUncaughtInvariant
<1> QED BY <1>1, <1>2, AgreementFromSafeUncaught, PTL



KnownTranClosureInvT ==
  \A s \in SafeAcceptors : TranClosure(known_messages[s]) = known_messages[s]

LEMMA InitKnownClosureT == Init => KnownTranClosureInvT
<1> SUFFICES ASSUME Init PROVE KnownTranClosureInvT  OBVIOUS
<1>1. known_messages = [s \in SafeAcceptors |-> {}]  BY DEF Init
<1> SUFFICES ASSUME NEW s \in SafeAcceptors PROVE TranClosure(known_messages[s]) = known_messages[s]
  BY DEF KnownTranClosureInvT
<1>2. known_messages[s] = {}  BY <1>1
<1>3. TranClosure({}) = {}  BY DEF TranClosure
<1> QED BY <1>2, <1>3

LEMMA KnownClosureStepT ==
  Inv /\ KnownTranClosureInvT /\ [Next]_vars => KnownTranClosureInvT'
<1> SUFFICES ASSUME Inv, KnownTranClosureInvT, [Next]_vars PROVE KnownTranClosureInvT'  OBVIOUS
<1>i. /\ Network \in SUBSET Messages
      /\ known_messages \in [SafeAcceptors -> SUBSET Messages]
      /\ IsFiniteSet(Network)
      /\ (\A s \in SafeAcceptors : known_messages[s] \subseteq Network)
      /\ (\A z \in Network : TranExclusive(z) \subseteq Network)
  BY DEF Inv
<1>2. CASE vars' = vars
  BY <1>2, KnownTranClosureInvT DEF KnownTranClosureInvT, vars
<1>3. CASE \E self \in SafeAcceptors \times Messages : safe_acceptor_receives_message(self)
  <2>1. PICK pp \in SafeAcceptors \times Messages : safe_acceptor_receives_message(pp)  BY <1>3
  <2> DEFINE self == pp[1]
  <2> DEFINE x == pp[2]
  <2>2. /\ x \in Network
        /\ TranExclusive(x) \subseteq known_messages[self]
        /\ known_messages' = [known_messages EXCEPT ![self] = known_messages[self] \cup {x}]
     BY <2>1 DEF safe_acceptor_receives_message
  <2>1a. self \in SafeAcceptors  BY <2>1
  <2>kself. known_messages'[self] = known_messages[self] \cup {x}  BY <2>2, <1>i, <2>1a
  <2> SUFFICES ASSUME NEW s \in SafeAcceptors PROVE TranClosure(known_messages'[s]) = known_messages'[s]
    BY DEF KnownTranClosureInvT
  <2>selfcase. CASE s = self
    <3>old. TranClosure(known_messages[self]) = known_messages[self]  BY KnownTranClosureInvT, <2>1a DEF KnownTranClosureInvT
    <3>1. TranClosure(known_messages[self] \cup {x}) = TranClosure(known_messages[self]) \cup TranClosure({x})
      BY DEF TranClosure
    <3>2. TranClosure({x}) = Tran(x)  BY DEF TranClosure
    <3>3. TranClosure(known_messages'[self]) = known_messages[self] \cup Tran(x)
      BY <2>kself, <3>1, <3>2, <3>old
    <3>4. Tran(x) = {x} \cup TranExclusive(x)  BY DEF Tran, TranExclusive
    <3>5. TranExclusive(x) \subseteq known_messages[self]  BY <2>2
    <3>6. Tran(x) \subseteq known_messages'[self]  BY <3>4, <3>5, <2>kself
    <3>7. TranClosure(known_messages'[self]) \subseteq known_messages'[self]
      BY <3>3, <3>6, <2>kself
    <3>8. known_messages'[self] \subseteq TranClosure(known_messages'[self])  BY TranClosureExpanding
    <3>9. TranClosure(known_messages'[self]) = known_messages'[self]  BY <3>7, <3>8
    <3> QED BY <3>9, <2>selfcase
  <2>othercase. CASE s # self
    <3>1. known_messages'[s] = known_messages[s]  BY <2>2, <2>othercase, <1>i, <2>1a
    <3> QED BY <3>1, KnownTranClosureInvT DEF KnownTranClosureInvT
  <2> QED BY <2>selfcase, <2>othercase
<1>4. CASE \E self \in ByzantineAcceptors : byz(self)
  <2>1. PICK self \in ByzantineAcceptors : byz(self)  BY <1>4
  <2>k. known_messages' = known_messages  BY <2>1 DEF byz
  <2> QED BY <2>k, KnownTranClosureInvT DEF KnownTranClosureInvT
<1> QED BY <1>2, <1>3, <1>4 DEF Next

LEMMA KnownClosureHoldsT == Spec => []KnownTranClosureInvT
<1>1. Init => KnownTranClosureInvT  BY InitKnownClosureT
<1>2. Inv /\ KnownTranClosureInvT /\ [Next]_vars => KnownTranClosureInvT'  BY KnownClosureStepT
<1>3. Spec => []Inv  BY InvHolds
<1> QED BY <1>1, <1>2, <1>3, PTL DEF Spec

SelfSentBoundedInvT ==
  \A s \in SafeAcceptors : \A z \in Network :
    Sig(z) = s => TranExclusive(z) \subseteq known_messages[s] \cup {m \in Network : Sig(m) = s}

LEMMA InitSelfSentT == Init => SelfSentBoundedInvT
<1> SUFFICES ASSUME Init PROVE SelfSentBoundedInvT  OBVIOUS
<1>1. Network = {}  BY DEF Init
<1> QED BY <1>1 DEF SelfSentBoundedInvT

LEMMA SelfSentStepT ==
  Inv /\ SelfSentBoundedInvT /\ [Next]_vars => SelfSentBoundedInvT'
<1> SUFFICES ASSUME Inv, SelfSentBoundedInvT, [Next]_vars PROVE SelfSentBoundedInvT'  OBVIOUS
<1>i. /\ Network \in SUBSET Messages
      /\ known_messages \in [SafeAcceptors -> SUBSET Messages]
      /\ IsFiniteSet(Network)
      /\ (\A s \in SafeAcceptors : known_messages[s] \subseteq Network)
      /\ (\A z \in Network : TranExclusive(z) \subseteq Network)
  BY DEF Inv
<1>2. CASE vars' = vars
  BY <1>2, SelfSentBoundedInvT DEF SelfSentBoundedInvT, vars
<1>3. CASE \E self \in SafeAcceptors \times Messages : safe_acceptor_receives_message(self)
  <2>1. PICK pp \in SafeAcceptors \times Messages : safe_acceptor_receives_message(pp)  BY <1>3
  <2> DEFINE self == pp[1]
  <2> DEFINE x == pp[2]
  <2>2. /\ x \in Network
        /\ TranExclusive(x) \subseteq known_messages[self]
        /\ known_messages' = [known_messages EXCEPT ![self] = known_messages[self] \cup {x}]
        /\ Network' = (LET T == (known_messages'[self] \cup {x})
                                  \cup {m \in Network : Sig(m) = self} IN
                       IF \E y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T
                         THEN Network \cup {CHOOSE y \in (Messages \ Proposals) :
                                             Sig(y) = self /\ TranExclusive(y) = T}
                         ELSE Network)
     BY <2>1 DEF safe_acceptor_receives_message
  <2>1a. self \in SafeAcceptors  BY <2>1
  <2>kself. known_messages'[self] = known_messages[self] \cup {x}  BY <2>2, <1>i, <2>1a
  <2> DEFINE T == (known_messages'[self] \cup {x}) \cup {m \in Network : Sig(m) = self}
  <2>net. Network' = (IF \E y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T
                        THEN Network \cup {CHOOSE y \in (Messages \ Proposals) :
                                            Sig(y) = self /\ TranExclusive(y) = T}
                        ELSE Network)
     BY <2>2
  <2>ndisj. \/ Network' = Network
            \/ \E y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T /\ Network' = Network \cup {y}
    <3>1. CASE \E y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T
      <4> DEFINE y0 == CHOOSE y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T
      <4>1. y0 \in (Messages \ Proposals) /\ Sig(y0) = self /\ TranExclusive(y0) = T  BY <3>1
      <4>2. Network' = Network \cup {y0}  BY <2>net, <3>1
      <4> QED  BY <4>1, <4>2
    <3>2. CASE ~(\E y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T)
      BY <2>net, <3>2
    <3> QED  BY <3>1, <3>2
  <2> SUFFICES ASSUME NEW s \in SafeAcceptors, NEW z \in Network', Sig(z) = s
               PROVE TranExclusive(z) \subseteq known_messages'[s] \cup {m \in Network' : Sig(m) = s}
    BY DEF SelfSentBoundedInvT
  <2>netmono. Network \subseteq Network'  BY <2>ndisj
  <2>knownmono. known_messages[s] \subseteq known_messages'[s]  BY <2>2, <2>1a, <1>i
  <2>zcase. z \in Network \/ (\E y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T /\ z = y)
    BY <2>ndisj
  <2>old. CASE z \in Network
    <3>old0. TranExclusive(z) \subseteq known_messages[s] \cup {m \in Network : Sig(m) = s}
      BY <2>old, SelfSentBoundedInvT DEF SelfSentBoundedInvT
    <3>sub. {m \in Network : Sig(m) = s} \subseteq {m \in Network' : Sig(m) = s}  BY <2>netmono
    <3> QED BY <3>old0, <3>sub, <2>knownmono
  <2>new. CASE \E y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T /\ z = y
    <3> PICK y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T /\ z = y  BY <2>new
    <3>seq. s = self  OBVIOUS
    <3>tez. TranExclusive(z) = T  OBVIOUS
    <3>tsub. {m \in Network : Sig(m) = self} \subseteq {m \in Network' : Sig(m) = self}  BY <2>netmono
    <3>tinT. T \subseteq known_messages'[self] \cup {m \in Network' : Sig(m) = self}  BY <3>tsub, <2>kself
    <3> QED BY <3>tez, <3>tinT, <3>seq
  <2> QED BY <2>zcase, <2>old, <2>new
<1>4. CASE \E self \in ByzantineAcceptors : byz(self)
  <2>1. PICK self \in ByzantineAcceptors : byz(self)  BY <1>4
  <2>2. PICK y \in {z \in Messages : Sig(z) = self /\ TranExclusive(z) \subseteq Network} :
              Network' = (Network \cup {y})
     BY <2>1 DEF byz
  <2>k. known_messages' = known_messages  BY <2>1 DEF byz
  <2>selfnotsafe. self \notin SafeAcceptors  BY <2>1 DEF ByzantineAcceptors
  <2> SUFFICES ASSUME NEW s \in SafeAcceptors, NEW z \in Network', Sig(z) = s
               PROVE TranExclusive(z) \subseteq known_messages'[s] \cup {m \in Network' : Sig(m) = s}
    BY DEF SelfSentBoundedInvT
  <2>netmono. Network \subseteq Network'  BY <2>2
  <2>ynotsafe. z # y
    <3> SUFFICES ASSUME z = y PROVE FALSE  OBVIOUS
    <3>1. Sig(z) = self  BY <2>2
    <3> QED BY <3>1, <2>selfnotsafe
  <2>zold. z \in Network  BY <2>2, <2>ynotsafe
  <2>old0. TranExclusive(z) \subseteq known_messages[s] \cup {m \in Network : Sig(m) = s}
    BY <2>zold, SelfSentBoundedInvT DEF SelfSentBoundedInvT
  <2>sub. {m \in Network : Sig(m) = s} \subseteq {m \in Network' : Sig(m) = s}  BY <2>netmono
  <2> QED BY <2>old0, <2>sub, <2>k
<1> QED BY <1>2, <1>3, <1>4 DEF Next

LEMMA SelfSentHoldsT == Spec => []SelfSentBoundedInvT
<1>1. Init => SelfSentBoundedInvT  BY InitSelfSentT
<1>2. Inv /\ SelfSentBoundedInvT /\ [Next]_vars => SelfSentBoundedInvT'  BY SelfSentStepT
<1>3. Spec => []Inv  BY InvHolds
<1> QED BY <1>1, <1>2, <1>3, PTL DEF Spec

SelfSentNotProposalInvT ==
  \A s \in SafeAcceptors : \A z \in Network : Sig(z) = s => ~IsProposal(z)

LEMMA InitSelfSentNotProposalT == Init => SelfSentNotProposalInvT
<1> SUFFICES ASSUME Init PROVE SelfSentNotProposalInvT  OBVIOUS
<1>1. Network = {}  BY DEF Init
<1> QED BY <1>1 DEF SelfSentNotProposalInvT

LEMMA SelfSentNotProposalStepT ==
  Inv /\ SelfSentNotProposalInvT /\ [Next]_vars => SelfSentNotProposalInvT'
<1> SUFFICES ASSUME Inv, SelfSentNotProposalInvT, [Next]_vars PROVE SelfSentNotProposalInvT'  OBVIOUS
<1>2. CASE vars' = vars
  BY <1>2, SelfSentNotProposalInvT DEF SelfSentNotProposalInvT, vars
<1>3. CASE \E self \in SafeAcceptors \times Messages : safe_acceptor_receives_message(self)
  <2>1. PICK pp \in SafeAcceptors \times Messages : safe_acceptor_receives_message(pp)  BY <1>3
  <2> DEFINE self == pp[1]
  <2> DEFINE x == pp[2]
  <2>2. /\ x \in Network
        /\ TranExclusive(x) \subseteq known_messages[self]
        /\ known_messages' = [known_messages EXCEPT ![self] = known_messages[self] \cup {x}]
        /\ Network' = (LET T == (known_messages'[self] \cup {x})
                                  \cup {m \in Network : Sig(m) = self} IN
                       IF \E y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T
                         THEN Network \cup {CHOOSE y \in (Messages \ Proposals) :
                                             Sig(y) = self /\ TranExclusive(y) = T}
                         ELSE Network)
     BY <2>1 DEF safe_acceptor_receives_message
  <2> DEFINE T == (known_messages'[self] \cup {x}) \cup {m \in Network : Sig(m) = self}
  <2>net. Network' = (IF \E y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T
                        THEN Network \cup {CHOOSE y \in (Messages \ Proposals) :
                                            Sig(y) = self /\ TranExclusive(y) = T}
                        ELSE Network)
     BY <2>2
  <2>ndisj. \/ Network' = Network
            \/ \E y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T /\ Network' = Network \cup {y}
    <3>1. CASE \E y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T
      <4> DEFINE y0 == CHOOSE y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T
      <4>1. y0 \in (Messages \ Proposals) /\ Sig(y0) = self /\ TranExclusive(y0) = T  BY <3>1
      <4>2. Network' = Network \cup {y0}  BY <2>net, <3>1
      <4> QED  BY <4>1, <4>2
    <3>2. CASE ~(\E y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T)
      BY <2>net, <3>2
    <3> QED  BY <3>1, <3>2
  <2> SUFFICES ASSUME NEW s \in SafeAcceptors, NEW z \in Network', Sig(z) = s
               PROVE ~IsProposal(z)
    BY DEF SelfSentNotProposalInvT
  <2>zcase. z \in Network \/ (\E y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T /\ z = y)
    BY <2>ndisj
  <2>old. CASE z \in Network
    BY <2>old, SelfSentNotProposalInvT DEF SelfSentNotProposalInvT
  <2>new. CASE \E y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T /\ z = y
    <3> PICK y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T /\ z = y  BY <2>new
    <3>ynotprop. y \notin Proposals  OBVIOUS
    <3> QED BY <3>ynotprop DEF IsProposal
  <2> QED BY <2>zcase, <2>old, <2>new
<1>4. CASE \E self \in ByzantineAcceptors : byz(self)
  <2>1. PICK self \in ByzantineAcceptors : byz(self)  BY <1>4
  <2>2. PICK y \in {z \in Messages : Sig(z) = self /\ TranExclusive(z) \subseteq Network} :
              Network' = (Network \cup {y})
     BY <2>1 DEF byz
  <2>selfnotsafe. self \notin SafeAcceptors  BY <2>1 DEF ByzantineAcceptors
  <2> SUFFICES ASSUME NEW s \in SafeAcceptors, NEW z \in Network', Sig(z) = s
               PROVE ~IsProposal(z)
    BY DEF SelfSentNotProposalInvT
  <2>ynotsafe. z # y
    <3> SUFFICES ASSUME z = y PROVE FALSE  OBVIOUS
    <3>1. Sig(z) = self  BY <2>2
    <3> QED BY <3>1, <2>selfnotsafe
  <2>zold. z \in Network  BY <2>2, <2>ynotsafe
  <2> QED BY <2>zold, SelfSentNotProposalInvT DEF SelfSentNotProposalInvT
<1> QED BY <1>2, <1>3, <1>4 DEF Next

LEMMA SelfSentNotProposalHoldsT == Spec => []SelfSentNotProposalInvT
<1>1. Init => SelfSentNotProposalInvT  BY InitSelfSentNotProposalT
<1>2. Inv /\ SelfSentNotProposalInvT /\ [Next]_vars => SelfSentNotProposalInvT'  BY SelfSentNotProposalStepT
<1>3. Spec => []Inv  BY InvHolds
<1> QED BY <1>1, <1>2, <1>3, PTL DEF Spec

LEMMA TranClosureOfTGenT ==
  ASSUME MessageInterfaceAssumptions, NEW KM \in SUBSET Messages, NEW NW \in SUBSET Messages, NEW s,
         TranClosure(KM) = KM,
         \A z \in NW : Sig(z) = s => TranExclusive(z) \subseteq KM \cup {m \in NW : Sig(m) = s}
  PROVE TranClosure(KM \cup {m \in NW : Sig(m) = s}) = KM \cup {m \in NW : Sig(m) = s}
<1> DEFINE SS == {m \in NW : Sig(m) = s}
<1> DEFINE T == KM \cup SS
<1>ssb. \A z \in SS : TranExclusive(z) \subseteq T
  <2> SUFFICES ASSUME NEW z \in SS PROVE TranExclusive(z) \subseteq T  OBVIOUS
  <2>1. z \in NW /\ Sig(z) = s  OBVIOUS
  <2> QED BY <2>1
<1>tcSS. TranClosure(SS) \subseteq T
  <2> SUFFICES ASSUME NEW z \in TranClosure(SS) PROVE z \in T  OBVIOUS
  <2>1. PICK w \in SS : z \in Tran(w)  BY DEF TranClosure
  <2>2. z = w \/ z \in TranExclusive(w)  BY <2>1 DEF Tran, TranExclusive
  <2>3. TranExclusive(w) \subseteq T  BY <2>1, <1>ssb
  <2> QED BY <2>1, <2>2, <2>3
<1>tcT. TranClosure(T) = TranClosure(KM) \cup TranClosure(SS)  BY TranClosureUnion
<1>sub1. TranClosure(T) \subseteq T  BY <1>tcT, <1>tcSS
<1>sub2. T \subseteq TranClosure(T)  BY TranClosureExpanding
<1> QED BY <1>sub1, <1>sub2

LEMMA CaughtSMonoT ==
  ASSUME NEW M1, NEW M2, M1 \subseteq M2
  PROVE CaughtS(M1) \subseteq CaughtS(M2)
BY DEF CaughtS

LEMMA LeFromEqT == ASSUME NEW p \in Ballots, NEW q \in Ballots, p = q PROVE p <= q
BY DEF Ballots

LEMMA LeTransBallotsT ==
  ASSUME NEW p \in Ballots, NEW q \in Ballots, NEW r \in Ballots, p <= q, q <= r
  PROVE p <= r
BY DEF Ballots

LEMMA EqFromLeGeBallotsT ==
  ASSUME NEW p \in Ballots, NEW q \in Ballots, p <= q, p >= q
  PROVE p = q
BY DEF Ballots

OneBInvariantT ==
  \A s \in SafeAcceptors :
  \A b \in Ballots :
  \A p \in known_messages[s] :
  (/\ B(p) = b
   /\ IsProposal(p)
   /\ \A xx \in known_messages[s] : IsProposal(xx) => B(xx) <= b
  ) => \E oneb \in Network :
  (/\ B(oneb) = b
   /\ Sig(oneb) = s
   /\ IsOneB(oneb)
  )

LEMMA InitOneBT == Init => OneBInvariantT
<1> SUFFICES ASSUME Init PROVE OneBInvariantT  OBVIOUS
<1>1. known_messages = [s \in SafeAcceptors |-> {}]  BY DEF Init
<1> QED BY <1>1 DEF OneBInvariantT

\* Core construction: within a learn step where self learns a genuinely-new
\* ballot-b proposal x with no other ballot-b proposal already known, the
\* forced-send mechanism's target set M is provably non-empty (AlwaysANewOneB),
\* and ANY witness the CHOOSE picks structurally satisfies B=b and IsOneB --
\* regardless of which specific witness is chosen.
LEMMA OneBConstructT ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions,
         Inv, KnownTranClosureInvT, SelfSentBoundedInvT, SelfSentNotProposalInvT,
         NEW self \in SafeAcceptors, NEW x \in Messages, NEW b \in Ballots,
         TranExclusive(x) \subseteq known_messages[self],
         x \notin known_messages[self],
         IsProposal(x), B(x) = b,
         \A ww \in known_messages[self] : IsProposal(ww) => B(ww) # b,
         \A ww \in known_messages[self] : IsProposal(ww) => B(ww) <= b,
         self \notin CaughtS(TranClosure((known_messages[self] \cup {x})
                                          \cup {mm \in Network : Sig(mm) = self}))
  PROVE \E y \in (Messages \ Proposals) :
          /\ Sig(y) = self
          /\ TranExclusive(y) = (known_messages[self] \cup {x}) \cup {mm \in Network : Sig(mm) = self}
          /\ B(y) = b
          /\ IsOneB(y)
<1>i. /\ Network \in SUBSET Messages
      /\ known_messages \in [SafeAcceptors -> SUBSET Messages]
      /\ IsFiniteSet(Network)
      /\ (\A s \in SafeAcceptors : known_messages[s] \subseteq Network)
  BY DEF Inv
<1>mi. TranFinite /\ TypeOKMessageInterface /\ AlwaysAProposal /\ AlwaysANewOneB
  BY DEF MessageInterfaceAssumptions
<1>selfacc. self \in Acceptors  BY SafeAcceptorsSubsetAcceptors
<1> DEFINE KP == known_messages[self] \cup {x}
<1> DEFINE T == KP \cup {mm \in Network : Sig(mm) = self}
<1>kpmsgs. KP \subseteq Messages  BY <1>i
<1>tmsgs. T \subseteq Messages  BY <1>kpmsgs, <1>i
<1>tfin. IsFiniteSet(T)
  <2>0. known_messages[self] \subseteq Network  BY <1>i
  <2>0b. IsFiniteSet(known_messages[self])  BY <2>0, <1>i, FS_Subset
  <2>1. IsFiniteSet(KP)  BY <2>0b, FS_AddElement
  <2>2. IsFiniteSet({mm \in Network : Sig(mm) = self})  BY <1>i, FS_Subset
  <2> QED BY <2>1, <2>2, FS_Union
<1>noneknown. \A w \in known_messages[self] : B(w) # b
  <2> SUFFICES ASSUME NEW w \in known_messages[self], B(w) = b PROVE FALSE  OBVIOUS
  <2>wm. w \in Messages  BY <1>i
  <2>ach. \E q \in Tran(w) : IsProposal(q) /\ B(q) = b  BY <2>wm, BAchievedByProposal
  <2> PICK q \in Tran(w) : IsProposal(q) /\ B(q) = b  BY <2>ach
  <2>qk. q \in known_messages[self]  BY KnownTranClosureInvT DEF KnownTranClosureInvT, TranClosure
  <2> QED BY <2>qk
<1>xpropbal. ProposalBal(x) = b
  <2>ach. \E q \in Tran(x) : IsProposal(q) /\ ProposalBal(q) = B(x) /\ B(q) = B(x)  BY BAchievedByProposal
  <2> PICK q \in Tran(x) : IsProposal(q) /\ ProposalBal(q) = B(x) /\ B(q) = B(x)  BY <2>ach
  <2>qcase. q = x \/ q \in TranExclusive(x)  BY DEF Tran, TranExclusive
  <2>notother. q \in TranExclusive(x) => FALSE
    <3> SUFFICES ASSUME q \in TranExclusive(x) PROVE FALSE  OBVIOUS
    <3>1. q \in known_messages[self]  OBVIOUS
    <3> QED BY <3>1
  <2> QED BY <2>qcase, <2>notother
<1>tbound. \A w \in T : B(w) <= b
  <2> SUFFICES ASSUME NEW w \in T PROVE B(w) <= b  OBVIOUS
  <2>wm. w \in Messages  BY <1>tmsgs
  <2>ach. \E q \in Tran(w) : IsProposal(q) /\ B(q) = B(w)  BY <2>wm, BAchievedByProposal
  <2> PICK q \in Tran(w) : IsProposal(q) /\ B(q) = B(w)  BY <2>ach
  <2>kpcase. CASE w \in KP
    <3>qw. q = w \/ q \in TranExclusive(w)  BY DEF Tran, TranExclusive
    <3>xcase. CASE w = x
      <4>1. B(w) = B(x)  BY <3>xcase
      <4>2. B(x) = b  OBVIOUS
      <4>3. B(w) = b  BY <4>1, <4>2
      <4>4. b \in Ballots  OBVIOUS
      <4>5. B(w) \in Ballots  BY <4>3, <4>4
      <4> QED BY <4>3, <4>4, <4>5, LeFromEqT
    <3>kcase. CASE w \in known_messages[self]
      <4>1. q = w \/ q \in known_messages[self]
        <5>1. TranExclusive(w) \subseteq known_messages[self]
          <6>a. Tran(w) \subseteq TranClosure(known_messages[self])  BY <3>kcase DEF TranClosure
          <6>b. TranClosure(known_messages[self]) = known_messages[self]
            BY KnownTranClosureInvT DEF KnownTranClosureInvT
          <6>c. TranExclusive(w) \subseteq Tran(w)  BY DEF Tran, TranExclusive
          <6> QED BY <6>a, <6>b, <6>c
        <5> QED BY <3>qw, <5>1
      <4>2. q \in known_messages[self]  BY <4>1, <3>kcase
      <4>3. IsProposal(q)  OBVIOUS
      <4>4. B(q) <= b  BY <4>2, <4>3
      <4>5. B(q) = B(w)  OBVIOUS
      <4> QED BY <4>4, <4>5
    <3> QED BY <3>xcase, <3>kcase, <2>kpcase
  <2>sscase. CASE w \in {mm \in Network : Sig(mm) = self}
    <3>notprop. ~IsProposal(w)
      <4>1. w \in Network /\ Sig(w) = self  BY <2>sscase
      <4> QED BY <4>1, SelfSentNotProposalInvT DEF SelfSentNotProposalInvT
    <3>qnw. q # w  BY <3>notprop
    <3>qte. q \in TranExclusive(w)  BY <3>qnw DEF Tran, TranExclusive
    <3>bound2. TranExclusive(w) \subseteq known_messages[self] \cup {mm \in Network : Sig(mm) = self}
      BY <2>sscase, SelfSentBoundedInvT DEF SelfSentBoundedInvT
    <3>qkorself. q \in known_messages[self] \/ q \in {mm \in Network : Sig(mm) = self}
      BY <3>qte, <3>bound2
    <3>qisprop. IsProposal(q)  OBVIOUS
    <3>notselfprop. q \notin {mm \in Network : Sig(mm) = self}
      <4> SUFFICES ASSUME q \in {mm \in Network : Sig(mm) = self} PROVE FALSE  OBVIOUS
      <4>1. q \in Network /\ Sig(q) = self  OBVIOUS
      <4> QED BY <4>1, <3>qisprop, SelfSentNotProposalInvT DEF SelfSentNotProposalInvT
    <3>qk. q \in known_messages[self]  BY <3>qkorself, <3>notselfprop
    <3>qbound. B(q) <= b  BY <3>qk, <3>qisprop
    <3>qbw. B(q) = B(w)  OBVIOUS
    <3> QED BY <3>qbound, <3>qbw
  <2> QED BY <2>kpcase, <2>sscase
<1>tcT. TranClosure(T) = T
  <2>kc. TranClosure(KP) = KP
    <3>1. TranClosure(known_messages[self]) = known_messages[self]
      BY KnownTranClosureInvT DEF KnownTranClosureInvT
    <3>2. TranClosure({x}) = Tran(x)  BY TranClosureSingleton
    <3>3. TranClosure(KP) = TranClosure(known_messages[self]) \cup TranClosure({x})  BY TranClosureUnion
    <3>4. TranExclusive(x) \subseteq KP  OBVIOUS
    <3>5. Tran(x) \subseteq KP
      <4>a. x \in KP  OBVIOUS
      <4>b. Tran(x) = {x} \cup TranExclusive(x)  BY DEF Tran, TranExclusive
      <4> QED BY <3>4, <4>a, <4>b
    <3> QED BY <3>1, <3>2, <3>3, <3>5, TranClosureExpanding
  <2>ssb. \A z \in Network :
            Sig(z) = self => TranExclusive(z) \subseteq KP \cup {mm \in Network : Sig(mm) = self}
    <3> SUFFICES ASSUME NEW z \in Network, Sig(z) = self
                 PROVE TranExclusive(z) \subseteq KP \cup {mm \in Network : Sig(mm) = self}  OBVIOUS
    <3>1. TranExclusive(z) \subseteq known_messages[self] \cup {mm \in Network : Sig(mm) = self}
      BY SelfSentBoundedInvT DEF SelfSentBoundedInvT
    <3> QED BY <3>1
  <2>tcSS. TranClosure({mm \in Network : Sig(mm) = self}) \subseteq T
    <3> SUFFICES ASSUME NEW z \in TranClosure({mm \in Network : Sig(mm) = self}) PROVE z \in T  OBVIOUS
    <3>1. PICK w \in {mm \in Network : Sig(mm) = self} : z \in Tran(w)  BY DEF TranClosure
    <3>2. z = w \/ z \in TranExclusive(w)  BY <3>1 DEF Tran, TranExclusive
    <3>3. w \in Network /\ Sig(w) = self  BY <3>1
    <3>4. TranExclusive(w) \subseteq KP \cup {mm \in Network : Sig(mm) = self}  BY <3>3, <2>ssb
    <3> QED BY <3>1, <3>2, <3>4
  <2>tcTeq. TranClosure(T) = TranClosure(KP) \cup TranClosure({mm \in Network : Sig(mm) = self})
    BY TranClosureUnion
  <2>sub1. TranClosure(T) \subseteq T  BY <2>tcTeq, <2>kc, <2>tcSS
  <2>sub2. T \subseteq TranClosure(T)  BY TranClosureExpanding
  <2> QED BY <2>sub1, <2>sub2
<1>tset. {z \in TranClosure(T) : B(z) = b} = {x}
  <2> SUFFICES ASSUME NEW z \in TranClosure(T), B(z) = b PROVE z = x  BY <1>tcT
  <2>zt. z \in T  BY <1>tcT
  <2>ach. \E q \in Tran(z) : IsProposal(q) /\ B(q) = b  BY <1>tmsgs, <2>zt, BAchievedByProposal
  <2> PICK q \in Tran(z) : IsProposal(q) /\ B(q) = b  BY <2>ach
  <2>kpcase. CASE z \in KP
    <3>qz. q = z \/ q \in TranExclusive(z)  BY DEF Tran, TranExclusive
    <3>xcase. CASE z = x  BY <3>xcase
    <3>kcase. CASE z \in known_messages[self]
      <4>1. q = z \/ q \in known_messages[self]
        <5>1. TranExclusive(z) \subseteq known_messages[self]
          BY <3>kcase, KnownTranClosureInvT DEF KnownTranClosureInvT, TranClosure, Tran
        <5> QED BY <3>qz, <5>1
      <4>2. CASE q = z  BY <4>2, <3>kcase
      <4>3. CASE q \in known_messages[self]  BY <4>3, <1>noneknown
      <4> QED BY <4>1, <4>2, <4>3
    <3> QED BY <3>xcase, <3>kcase, <2>kpcase
  <2>sscase. CASE z \in {mm \in Network : Sig(mm) = self}
    <3>notprop. ~IsProposal(z)
      <4>1. z \in Network /\ Sig(z) = self  BY <2>sscase
      <4> QED BY <4>1, SelfSentNotProposalInvT DEF SelfSentNotProposalInvT
    <3>qnz. q # z  BY <3>notprop
    <3>qte. q \in TranExclusive(z)  BY <3>qnz DEF Tran, TranExclusive
    <3>bound2. TranExclusive(z) \subseteq known_messages[self] \cup {mm \in Network : Sig(mm) = self}
      BY <2>sscase, SelfSentBoundedInvT DEF SelfSentBoundedInvT
    <3>qkorself. q \in known_messages[self] \/ q \in {mm \in Network : Sig(mm) = self}
      BY <3>qte, <3>bound2
    <3>qisprop. IsProposal(q)  OBVIOUS
    <3>notselfprop. q \notin {mm \in Network : Sig(mm) = self}
      <4> SUFFICES ASSUME q \in {mm \in Network : Sig(mm) = self} PROVE FALSE  OBVIOUS
      <4>1. q \in Network /\ Sig(q) = self  OBVIOUS
      <4> QED BY <4>1, <3>qisprop, SelfSentNotProposalInvT DEF SelfSentNotProposalInvT
    <3>qk. q \in known_messages[self]  BY <3>qkorself, <3>notselfprop
    <3>qbeqb. B(q) = b  OBVIOUS
    <3>qbneqb. B(q) # b  BY <3>qk, <1>noneknown
    <3> QED BY <3>qbeqb, <3>qbneqb
  <2>zdisj. z \in KP \/ z \in {mm \in Network : Sig(mm) = self}  BY <2>zt
  <2> QED BY <2>zdisj, <2>kpcase, <2>sscase
<1>xint. x \in TranClosure(T)  BY <1>tcT, TranClosureExpanding
<1>card1. Cardinality({z \in TranClosure(T) : B(z) = b}) = 1  BY <1>tset, FS_Singleton
<1>uncaught. self \notin CaughtS(TranClosure(T))  OBVIOUS \* matches the lemma's own hypothesis verbatim (T's literal expansion)
<1>anb. \E y \in Messages :
          /\ Sig(y) = self
          /\ self \notin Caught(y)
          /\ IsOneB(y)
          /\ TranExclusive(y) = TranClosure(T)
  BY <1>mi, <1>selfacc, <1>tmsgs, <1>tfin, <1>tbound, <1>card1, <1>uncaught DEF AlwaysANewOneB
<1> PICK y \in Messages :
      /\ Sig(y) = self
      /\ self \notin Caught(y)
      /\ IsOneB(y)
      /\ TranExclusive(y) = TranClosure(T)
  BY <1>anb
<1>ytc. TranExclusive(y) = T  BY <1>tcT
<1>ynotprop. y \notin Proposals  BY DEF IsOneB, IsProposal
<1>ybal. B(y) = b
  <2> DEFINE Cand == Proposals \cap Tran(y)
  <2>tranY. Tran(y) = {y} \cup T  BY <1>ytc DEF Tran, TranExclusive
  <2>candeq. Cand = Proposals \cap T
    <3>1. y \notin Proposals  BY <1>ynotprop
    <3> QED BY <2>tranY, <3>1
  <2>xincand. x \in Cand
    <3>a. x \in Proposals  BY DEF IsProposal
    <3>b. x \in T  OBVIOUS
    <3> QED BY <2>candeq, <3>a, <3>b
  <2>ubound. \A z \in Cand : ProposalBal(z) <= b
    <3> SUFFICES ASSUME NEW z \in Cand PROVE ProposalBal(z) <= b  OBVIOUS
    <3>1. z \in T  BY <2>candeq
    <3>2. IsProposal(z)  BY <2>candeq DEF IsProposal
    <3>3. z \in Messages  BY <3>1, <1>tmsgs
    <3>4. z \in GetProposals(z)
      <4>1. z \in Tran(z)  BY DEF Tran
      <4> QED BY <4>1, <2>candeq DEF GetProposals
    <3>5. ProposalBal(z) <= B(z)
      <4>fin. IsFiniteSet(GetProposals(z))
        <5>1. GetProposals(z) \subseteq Tran(z)  BY DEF GetProposals
        <5>2. IsFiniteSet(Tran(z))  BY <3>3, <1>mi DEF TranFinite
        <5> QED BY <5>1, <5>2, FS_Subset
      <4>sub. GetProposals(z) \subseteq Proposals  BY DEF GetProposals
      <4>ne. GetProposals(z) # {}  BY <3>4
      <4>choose. /\ B(z) \in {ProposalBal(w) : w \in GetProposals(z)}
                 /\ \A ww \in {ProposalBal(w) : w \in GetProposals(z)} : B(z) >= ww
        BY <4>fin, <4>sub, <4>ne, <1>mi, MaxBSetProperty DEF B
      <4>mem. ProposalBal(z) \in {ProposalBal(w) : w \in GetProposals(z)}  BY <3>4
      <4> QED BY <4>choose, <4>mem
    <3>6. B(z) <= b  BY <3>1, <1>tbound
    <3>7. ProposalBal(z) \in Ballots
      <4>1. MessageInterface.proposalbal \in [Proposals -> Ballots]  BY <1>mi DEF TypeOKMessageInterface
      <4>2. z \in Proposals  BY <3>2 DEF IsProposal
      <4> QED BY <4>1, <4>2 DEF ProposalBal
    <3>8. B(z) \in Ballots  BY <1>mi, <3>3, BBallot
    <3>9. b \in Ballots  OBVIOUS
    <3> QED BY <3>5, <3>6, <3>7, <3>8, <3>9, LeTransBallotsT
  <2>xbal. ProposalBal(x) = b  BY <1>xpropbal
  <2>candfin. IsFiniteSet(Cand)
    <3>ysub. Cand \subseteq Tran(y)  OBVIOUS
    <3>yfin. IsFiniteSet(Tran(y))  BY <1>mi DEF TranFinite
    <3> QED BY <3>ysub, <3>yfin, FS_Subset
  <2>candsub. Cand \subseteq Proposals  OBVIOUS
  <2>candne. Cand # {}  BY <2>xincand
  <2>ychoose. /\ B(y) \in {ProposalBal(w) : w \in Cand}
              /\ \A ww \in {ProposalBal(w) : w \in Cand} : B(y) >= ww
    BY <2>candfin, <2>candsub, <2>candne, <1>mi, MaxBSetProperty DEF B, GetProposals
  <2>yge. B(y) >= b
    <3>1. ProposalBal(x) \in {ProposalBal(w) : w \in Cand}  BY <2>xincand
    <3> QED BY <3>1, <2>ychoose, <2>xbal
  <2>yle. B(y) <= b
    <3>pw. PICK w \in Cand : B(y) = ProposalBal(w)  BY <2>ychoose
    <3> QED BY <3>pw, <2>ubound
  <2>yty. y \in Messages  OBVIOUS
  <2>ybalty. B(y) \in Ballots  BY <1>mi, <2>yty, BBallot
  <2>bty. b \in Ballots  OBVIOUS
  <2> QED BY <2>yge, <2>yle, <2>ybalty, <2>bty, EqFromLeGeBallotsT
<1>xney. x # y
  <2>xprop. x \in Proposals  BY DEF IsProposal
  <2> QED BY <2>xprop, <1>ynotprop
<1>yisoneb. IsOneB(y)
  <2>cardxy. {z \in Tran(y) : B(z) = b} = {x, y}
    <3>tranY. Tran(y) = {y} \cup T  BY <1>ytc DEF Tran, TranExclusive
    <3>seteq. {z \in T : B(z) = b} = {x}  BY <1>tset, <1>tcT
    <3> QED BY <3>tranY, <3>seteq, <1>ybal, <1>xney
  <2>card2. Cardinality({x, y}) = 2
    <3>1. IsFiniteSet({y})  BY FS_Singleton
    <3>2. Cardinality({y}) = 1  BY FS_Singleton
    <3>3. x \notin {y}  BY <1>xney
    <3>4. {x,y} = {x} \cup {y}  OBVIOUS
    <3> QED BY <3>1, <3>2, <3>3, <3>4, FS_AddElement
  <2> QED BY <2>cardxy, <2>card2, <1>ynotprop DEF IsOneB, IsProposal
<1> QED BY <1>ynotprop, <1>ytc, <1>ybal, <1>yisoneb DEF Proposals

\* Strengthens OneBConstructT's own \A w \in T : B(w) <= b bound: given that p is
\* the UNIQUE proposal ever sent with ballot > bal, and self hasn't yet learned
\* of p, everything self already knows (or has itself sent) must have ballot
\* <= bal, not just <= B(p). This is what lets the self-known/self-sent part of
\* a freshly-constructed OneB's ancestry land inside TerminatingProposal's M.
LEMMA SelfKnownBoundedByUniqueT ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions,
         Inv, KnownTranClosureInvT, SelfSentBoundedInvT, SelfSentNotProposalInvT,
         NEW self \in SafeAcceptors, NEW p \in Proposals, NEW bal \in Ballots,
         B(p) > bal,
         p \notin known_messages[self],
         \A z \in Proposals : ((<>(z \in Network)) /\ (B(z) > bal)) => (z = p),
         NEW w \in (known_messages[self] \cup {mm \in Network : Sig(mm) = self})
  PROVE B(w) <= bal
<1>i. /\ Network \in SUBSET Messages
      /\ known_messages \in [SafeAcceptors -> SUBSET Messages]
      /\ IsFiniteSet(Network)
      /\ (\A s \in SafeAcceptors : known_messages[s] \subseteq Network)
  BY DEF Inv
<1>mi. TranFinite /\ TypeOKMessageInterface /\ AlwaysAProposal
  BY DEF MessageInterfaceAssumptions
<1> DEFINE Uniq(z) == ((<>(z \in Network)) /\ (B(z) > bal)) => (z = p)
<1>uniqhyp. \A z \in Proposals : Uniq(z)  BY DEF Uniq
<1> HIDE DEF Uniq
<1>wor. w \in known_messages[self] \/ w \in {mm \in Network : Sig(mm) = self}  OBVIOUS
<1>wmsg. w \in Messages  BY <1>wor, <1>i
<1>wnet. w \in Network  BY <1>wor, <1>i
<1>wte. TranExclusive(w) \subseteq known_messages[self] \cup {mm \in Network : Sig(mm) = self}
  <2>1. CASE w \in known_messages[self]
    <3>a. Tran(w) \subseteq TranClosure(known_messages[self])  BY <2>1 DEF TranClosure
    <3>b. TranClosure(known_messages[self]) = known_messages[self]
      BY KnownTranClosureInvT DEF KnownTranClosureInvT
    <3>c. TranExclusive(w) \subseteq Tran(w)  BY DEF Tran, TranExclusive
    <3> QED BY <3>a, <3>b, <3>c
  <2>2. CASE w \in {mm \in Network : Sig(mm) = self}
    BY <2>2, SelfSentBoundedInvT DEF SelfSentBoundedInvT
  <2> QED BY <1>wor, <2>1, <2>2
<1>balnat. bal \in Nat  BY DEF Ballots
<1>bwnat. B(w) \in Ballots  BY <1>wmsg, <1>mi, BBallot
<1>case. B(w) <= bal \/ B(w) > bal  BY <1>bwnat, <1>balnat DEF Ballots
<1>casehigh. CASE B(w) > bal
  <2>ach. \E q \in Tran(w) : IsProposal(q) /\ B(q) = B(w)  BY <1>wmsg, BAchievedByProposal
  <2> PICK q \in Tran(w) : IsProposal(q) /\ B(q) = B(w)  BY <2>ach
  <2>qprop. q \in Proposals  BY DEF IsProposal
  <2>qbalpos. B(q) > bal  BY <1>casehigh
  <2>qcase. q = w \/ q \in TranExclusive(w)  BY DEF Tran, TranExclusive
  <2>qnet. q \in Network
    <3>1. CASE q = w  BY <3>1, <1>wnet
    <3>2. CASE q \in TranExclusive(w)  BY <3>2, <1>wte, <1>i
    <3> QED BY <2>qcase, <3>1, <3>2
  <2>qevernet. <>(q \in Network)  BY <2>qnet, PTL
  <2>uniqq. Uniq(q)  BY <2>qprop, <1>uniqhyp
  <2>qisp. q = p  BY <2>uniqq, <2>qevernet, <2>qbalpos DEF Uniq
  <2>notself. p \notin {mm \in Network : Sig(mm) = self}
    <3>allns. \A mm \in Network : Sig(mm) = self => ~IsProposal(mm)
      BY SelfSentNotProposalInvT DEF SelfSentNotProposalInvT
    <3> QED BY <3>allns DEF IsProposal
  <2>qnotw. q # w
    <3>1. CASE q = w
      <4>1. w = p  BY <3>1, <2>qisp
      <4>2. p \in known_messages[self]  BY <4>1, <1>wor, <2>notself
      <4> QED BY <4>2
    <3>2. CASE q # w  BY <3>2
    <3> QED BY <3>1, <3>2
  <2>qte. q \in TranExclusive(w)  BY <2>qcase, <2>qnotw
  <2>pinw. p \in TranExclusive(w)  BY <2>qte, <2>qisp
  <2>pkorself. p \in known_messages[self] \/ p \in {mm \in Network : Sig(mm) = self}
    BY <2>pinw, <1>wte
  <2>false. FALSE  BY <2>pkorself, <2>notself
  <2> QED BY <2>false
<1>caselow. CASE B(w) <= bal  BY <1>caselow
<1> QED BY <1>case, <1>casehigh, <1>caselow

\* Combines OneBConstructT (existence of a freshly-constructed OneB from self's
\* knowledge plus a newly-learned proposal p) with SelfKnownBoundedByUniqueT
\* (self's prior knowledge/self-sent messages all have ballot <= bal, given p's
\* uniqueness) to produce the EXACT shape DecideableProposalOneBFreshAny needs:
\* a witness oneb with TranExclusive(oneb) = TranClosure(known \cup {p}) for
\* some known \subseteq M (TerminatingProposal's own low-ballot-ever-sent set).
LEMMA OneBConstructBoundedT ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions,
         Inv, KnownTranClosureInvT, SelfSentBoundedInvT, SelfSentNotProposalInvT,
         NEW self \in SafeAcceptors, NEW p \in Proposals, NEW bal \in Ballots,
         TranExclusive(p) \subseteq known_messages[self],
         p \notin known_messages[self],
         \A ww \in known_messages[self] : IsProposal(ww) => B(ww) # B(p),
         \A ww \in known_messages[self] : IsProposal(ww) => B(ww) <= B(p),
         self \notin CaughtS(TranClosure((known_messages[self] \cup {p})
                                          \cup {mm \in Network : Sig(mm) = self})),
         B(p) > bal,
         \A z \in Proposals : ((<>(z \in Network)) /\ (B(z) > bal)) => (z = p)
  PROVE \E known \in SUBSET Messages :
        /\ known \subseteq Network
        /\ self \notin CaughtS(TranClosure(known \cup {p}))
        /\ (\A w \in known : (B(w) <= bal) /\ (<>(w \in Network)))
        /\ \E y \in (Messages \ Proposals) :
             /\ Sig(y) = self
             /\ TranExclusive(y) = TranClosure(known \cup {p})
             /\ TranExclusive(y) = (known_messages[self] \cup {p}) \cup {mm \in Network : Sig(mm) = self}
             /\ B(y) = B(p)
             /\ IsOneB(y)
<1>i. /\ Network \in SUBSET Messages
      /\ known_messages \in [SafeAcceptors -> SUBSET Messages]
      /\ IsFiniteSet(Network)
      /\ (\A s \in SafeAcceptors : known_messages[s] \subseteq Network)
  BY DEF Inv
<1> DEFINE KP == known_messages[self] \cup {p}
<1> DEFINE SS == {mm \in Network : Sig(mm) = self}
<1> DEFINE T == KP \cup SS
<1>mi. TypeOKMessageInterface /\ TranFinite /\ AlwaysAProposal  BY DEF MessageInterfaceAssumptions
<1>pmsg. p \in Messages  BY <1>mi DEF TypeOKMessageInterface
<1>bpnat. B(p) \in Ballots  BY <1>pmsg, <1>mi, BBallot
<1>bpWit. \E bb \in Ballots : bb = B(p)  BY <1>bpnat
<1> PICK bb \in Ballots : bb = B(p)  BY <1>bpWit
<1>ex. \E y \in (Messages \ Proposals) :
         /\ Sig(y) = self
         /\ TranExclusive(y) = T
         /\ B(y) = bb
         /\ IsOneB(y)
  BY <1>pmsg, Inv, KnownTranClosureInvT, SelfSentBoundedInvT, SelfSentNotProposalInvT, OneBConstructT
    DEF IsProposal
<1> PICK y \in (Messages \ Proposals) :
      /\ Sig(y) = self
      /\ TranExclusive(y) = T
      /\ B(y) = bb
      /\ IsOneB(y)
  BY <1>ex
<1>known. known_messages[self] \subseteq Network  BY <1>i
<1>tcKP. TranClosure(KP) = KP
  <2>1. TranClosure(known_messages[self]) = known_messages[self]
    BY KnownTranClosureInvT DEF KnownTranClosureInvT
  <2>2. TranClosure({p}) = Tran(p)  BY TranClosureSingleton
  <2>3. TranClosure(KP) = TranClosure(known_messages[self]) \cup TranClosure({p})
    BY TranClosureUnion
  <2>4. TranExclusive(p) \subseteq KP  OBVIOUS
  <2>5. Tran(p) \subseteq KP
    <3>a. p \in KP  OBVIOUS
    <3>b. Tran(p) = {p} \cup TranExclusive(p)  BY DEF Tran, TranExclusive
    <3> QED BY <2>4, <3>a, <3>b
  <2> QED BY <2>1, <2>2, <2>3, <2>5, TranClosureExpanding
<1>ssb. \A z \in Network : Sig(z) = self => TranExclusive(z) \subseteq KP \cup SS
  <2> SUFFICES ASSUME NEW z \in Network, Sig(z) = self
               PROVE TranExclusive(z) \subseteq KP \cup SS  OBVIOUS
  <2>1. TranExclusive(z) \subseteq known_messages[self] \cup SS  BY SelfSentBoundedInvT DEF SelfSentBoundedInvT
  <2> QED BY <2>1
<1>tcSS. TranClosure(SS) \subseteq T
  <2> SUFFICES ASSUME NEW z \in TranClosure(SS) PROVE z \in T  OBVIOUS
  <2>1. PICK w \in SS : z \in Tran(w)  BY DEF TranClosure
  <2>2. z = w \/ z \in TranExclusive(w)  BY <2>1 DEF Tran, TranExclusive
  <2>3. w \in Network /\ Sig(w) = self  BY <2>1
  <2>4. TranExclusive(w) \subseteq KP \cup SS  BY <2>3, <1>ssb
  <2> QED BY <2>1, <2>2, <2>4
<1>tcTeq. TranClosure(T) = TranClosure(KP) \cup TranClosure(SS)  BY TranClosureUnion
<1>tcT. TranClosure(T) = T
  <2>sub1. TranClosure(T) \subseteq T  BY <1>tcTeq, <1>tcKP, <1>tcSS
  <2>sub2. T \subseteq TranClosure(T)  BY TranClosureExpanding
  <2> QED BY <2>sub1, <2>sub2
<1>pnotss. p \notin SS
  <2> SUFFICES ASSUME p \in SS PROVE FALSE  OBVIOUS
  <2>1. p \in Network /\ Sig(p) = self  OBVIOUS
  <2>2. ~IsProposal(p)  BY <2>1, SelfSentNotProposalInvT DEF SelfSentNotProposalInvT
  <2> QED BY <2>2 DEF IsProposal
<1> DEFINE known == known_messages[self] \cup SS
<1>keq. known \cup {p} = T  BY <1>pnotss
<1>tep. TranExclusive(y) = TranClosure(known \cup {p})  BY <1>keq, <1>tcT
<1>knownmsgs. known \subseteq Messages  BY <1>known, <1>i
<1>knownbound. \A w \in known : B(w) <= bal
  <2> SUFFICES ASSUME NEW w \in known PROVE B(w) <= bal  OBVIOUS
  <2>1. w \in known_messages[self] \/ w \in SS  BY DEF known
  <2> QED BY <2>1, MessageInterfaceAssumptions, LearnerGraphAssumptions, Inv,
             KnownTranClosureInvT, SelfSentBoundedInvT, SelfSentNotProposalInvT,
             SelfKnownBoundedByUniqueT
<1>knownnet. \A w \in known : w \in Network
  <2> SUFFICES ASSUME NEW w \in known PROVE w \in Network  OBVIOUS
  <2>1. w \in known_messages[self] \/ w \in SS  BY DEF known
  <2> QED BY <2>1, <1>known
<1>knownev. \A w \in known : (B(w) <= bal) /\ (<>(w \in Network))
  <2> SUFFICES ASSUME NEW w \in known
               PROVE B(w) <= bal /\ (<>(w \in Network))  OBVIOUS
  <2>1. B(w) <= bal  BY <1>knownbound
  <2>2. w \in Network  BY <1>knownnet
  <2>3. <>(w \in Network)  BY <2>2, PTL
  <2> QED BY <2>1, <2>3
<1>selfnotcaught. self \notin CaughtS(TranClosure(known \cup {p}))  BY <1>keq
<1>kWit. \E kk \in SUBSET Messages : kk = known  BY <1>knownmsgs
<1> PICK kk \in SUBSET Messages : kk = known  BY <1>kWit
<1> QED
  <2> WITNESS kk \in SUBSET Messages
  <2>1. kk \subseteq Network  BY <1>knownnet
  <2>2. self \notin CaughtS(TranClosure(kk \cup {p}))  BY <1>selfnotcaught
  <2>3. \A w \in kk : (B(w) <= bal) /\ (<>(w \in Network))  BY <1>knownev
  <2>4. \E y \in (Messages \ Proposals) :
          /\ Sig(y) = self
          /\ TranExclusive(y) = TranClosure(kk \cup {p})
          /\ TranExclusive(y) = (known_messages[self] \cup {p}) \cup {mm \in Network : Sig(mm) = self}
          /\ B(y) = B(p)
          /\ IsOneB(y)
    <3> WITNESS y \in (Messages \ Proposals)
    <3> QED BY <1>tep, <1>keq, <1>tcT
  <2> QED BY <2>1, <2>2, <2>3, <2>4

\* Companion to OneBConstructT: the B=b/IsOneB conclusion depends only on
\* Sig(y)=self and TranExclusive(y)=T (plus y not being a proposal), not on
\* how y was obtained -- so it applies uniformly to whichever witness the
\* model's CHOOSE actually picks, not just the one AlwaysANewOneB hands us.
LEMMA OneBAnyWitnessT ==
  ASSUME MessageInterfaceAssumptions,
         Inv, KnownTranClosureInvT, SelfSentBoundedInvT, SelfSentNotProposalInvT,
         NEW self \in SafeAcceptors, NEW x \in Messages, NEW b \in Ballots,
         TranExclusive(x) \subseteq known_messages[self],
         IsProposal(x), B(x) = b,
         \A ww \in known_messages[self] : IsProposal(ww) => B(ww) # b,
         \A ww \in known_messages[self] : IsProposal(ww) => B(ww) <= b,
         NEW y \in (Messages \ Proposals),
         Sig(y) = self,
         TranExclusive(y) = (known_messages[self] \cup {x}) \cup {mm \in Network : Sig(mm) = self}
  PROVE B(y) = b /\ IsOneB(y)
<1>i. /\ Network \in SUBSET Messages
      /\ known_messages \in [SafeAcceptors -> SUBSET Messages]
      /\ IsFiniteSet(Network)
      /\ (\A s \in SafeAcceptors : known_messages[s] \subseteq Network)
  BY DEF Inv
<1>mi. TranFinite /\ TypeOKMessageInterface /\ AlwaysAProposal
  BY DEF MessageInterfaceAssumptions
<1> DEFINE KP == known_messages[self] \cup {x}
<1> DEFINE T == KP \cup {mm \in Network : Sig(mm) = self}
<1>kpmsgs. KP \subseteq Messages  BY <1>i
<1>tmsgs. T \subseteq Messages  BY <1>kpmsgs, <1>i
<1>noneknown. \A w \in known_messages[self] : B(w) # b
  <2> SUFFICES ASSUME NEW w \in known_messages[self], B(w) = b PROVE FALSE  OBVIOUS
  <2>wm. w \in Messages  BY <1>i
  <2>ach. \E q \in Tran(w) : IsProposal(q) /\ B(q) = b  BY <2>wm, BAchievedByProposal
  <2> PICK q \in Tran(w) : IsProposal(q) /\ B(q) = b  BY <2>ach
  <2>qk. q \in known_messages[self]  BY KnownTranClosureInvT DEF KnownTranClosureInvT, TranClosure
  <2> QED BY <2>qk
<1>xpropbal. ProposalBal(x) = b
  <2>ach. \E q \in Tran(x) : IsProposal(q) /\ ProposalBal(q) = B(x) /\ B(q) = B(x)  BY BAchievedByProposal
  <2> PICK q \in Tran(x) : IsProposal(q) /\ ProposalBal(q) = B(x) /\ B(q) = B(x)  BY <2>ach
  <2>qcase. q = x \/ q \in TranExclusive(x)  BY DEF Tran, TranExclusive
  <2>notother. q \in TranExclusive(x) => FALSE
    <3> SUFFICES ASSUME q \in TranExclusive(x) PROVE FALSE  OBVIOUS
    <3>1. q \in known_messages[self]  OBVIOUS
    <3> QED BY <3>1
  <2> QED BY <2>qcase, <2>notother
<1>tbound. \A w \in T : B(w) <= b
  <2> SUFFICES ASSUME NEW w \in T PROVE B(w) <= b  OBVIOUS
  <2>wm. w \in Messages  BY <1>tmsgs
  <2>ach. \E q \in Tran(w) : IsProposal(q) /\ B(q) = B(w)  BY <2>wm, BAchievedByProposal
  <2> PICK q \in Tran(w) : IsProposal(q) /\ B(q) = B(w)  BY <2>ach
  <2>kpcase. CASE w \in KP
    <3>qw. q = w \/ q \in TranExclusive(w)  BY DEF Tran, TranExclusive
    <3>xcase. CASE w = x
      <4>1. B(w) = B(x)  BY <3>xcase
      <4>2. B(x) = b  OBVIOUS
      <4>3. B(w) = b  BY <4>1, <4>2
      <4>4. b \in Ballots  OBVIOUS
      <4>5. B(w) \in Ballots  BY <4>3, <4>4
      <4> QED BY <4>3, <4>4, <4>5, LeFromEqT
    <3>kcase. CASE w \in known_messages[self]
      <4>1. q = w \/ q \in known_messages[self]
        <5>1. TranExclusive(w) \subseteq known_messages[self]
          <6>a. Tran(w) \subseteq TranClosure(known_messages[self])  BY <3>kcase DEF TranClosure
          <6>b. TranClosure(known_messages[self]) = known_messages[self]
            BY KnownTranClosureInvT DEF KnownTranClosureInvT
          <6>c. TranExclusive(w) \subseteq Tran(w)  BY DEF Tran, TranExclusive
          <6> QED BY <6>a, <6>b, <6>c
        <5> QED BY <3>qw, <5>1
      <4>2. q \in known_messages[self]  BY <4>1, <3>kcase
      <4>3. IsProposal(q)  OBVIOUS
      <4>4. B(q) <= b  BY <4>2, <4>3
      <4>5. B(q) = B(w)  OBVIOUS
      <4> QED BY <4>4, <4>5
    <3> QED BY <3>xcase, <3>kcase, <2>kpcase
  <2>sscase. CASE w \in {mm \in Network : Sig(mm) = self}
    <3>notprop. ~IsProposal(w)
      <4>1. w \in Network /\ Sig(w) = self  BY <2>sscase
      <4> QED BY <4>1, SelfSentNotProposalInvT DEF SelfSentNotProposalInvT
    <3>qnw. q # w  BY <3>notprop
    <3>qte. q \in TranExclusive(w)  BY <3>qnw DEF Tran, TranExclusive
    <3>bound2. TranExclusive(w) \subseteq known_messages[self] \cup {mm \in Network : Sig(mm) = self}
      BY <2>sscase, SelfSentBoundedInvT DEF SelfSentBoundedInvT
    <3>qkorself. q \in known_messages[self] \/ q \in {mm \in Network : Sig(mm) = self}
      BY <3>qte, <3>bound2
    <3>qisprop. IsProposal(q)  OBVIOUS
    <3>notselfprop. q \notin {mm \in Network : Sig(mm) = self}
      <4> SUFFICES ASSUME q \in {mm \in Network : Sig(mm) = self} PROVE FALSE  OBVIOUS
      <4>1. q \in Network /\ Sig(q) = self  OBVIOUS
      <4> QED BY <4>1, <3>qisprop, SelfSentNotProposalInvT DEF SelfSentNotProposalInvT
    <3>qk. q \in known_messages[self]  BY <3>qkorself, <3>notselfprop
    <3>qbound. B(q) <= b  BY <3>qk, <3>qisprop
    <3>qbw. B(q) = B(w)  OBVIOUS
    <3> QED BY <3>qbound, <3>qbw
  <2> QED BY <2>kpcase, <2>sscase
<1>tcT. TranClosure(T) = T
  <2>kc. TranClosure(KP) = KP
    <3>1. TranClosure(known_messages[self]) = known_messages[self]
      BY KnownTranClosureInvT DEF KnownTranClosureInvT
    <3>2. TranClosure({x}) = Tran(x)  BY TranClosureSingleton
    <3>3. TranClosure(KP) = TranClosure(known_messages[self]) \cup TranClosure({x})  BY TranClosureUnion
    <3>4. TranExclusive(x) \subseteq KP  OBVIOUS
    <3>5. Tran(x) \subseteq KP
      <4>a. x \in KP  OBVIOUS
      <4>b. Tran(x) = {x} \cup TranExclusive(x)  BY DEF Tran, TranExclusive
      <4> QED BY <3>4, <4>a, <4>b
    <3> QED BY <3>1, <3>2, <3>3, <3>5, TranClosureExpanding
  <2>ssb. \A z \in Network :
            Sig(z) = self => TranExclusive(z) \subseteq KP \cup {mm \in Network : Sig(mm) = self}
    <3> SUFFICES ASSUME NEW z \in Network, Sig(z) = self
                 PROVE TranExclusive(z) \subseteq KP \cup {mm \in Network : Sig(mm) = self}  OBVIOUS
    <3>1. TranExclusive(z) \subseteq known_messages[self] \cup {mm \in Network : Sig(mm) = self}
      BY SelfSentBoundedInvT DEF SelfSentBoundedInvT
    <3> QED BY <3>1
  <2>tcSS. TranClosure({mm \in Network : Sig(mm) = self}) \subseteq T
    <3> SUFFICES ASSUME NEW z \in TranClosure({mm \in Network : Sig(mm) = self}) PROVE z \in T  OBVIOUS
    <3>1. PICK w \in {mm \in Network : Sig(mm) = self} : z \in Tran(w)  BY DEF TranClosure
    <3>2. z = w \/ z \in TranExclusive(w)  BY <3>1 DEF Tran, TranExclusive
    <3>3. w \in Network /\ Sig(w) = self  BY <3>1
    <3>4. TranExclusive(w) \subseteq KP \cup {mm \in Network : Sig(mm) = self}  BY <3>3, <2>ssb
    <3> QED BY <3>1, <3>2, <3>4
  <2>tcTeq. TranClosure(T) = TranClosure(KP) \cup TranClosure({mm \in Network : Sig(mm) = self})
    BY TranClosureUnion
  <2>sub1. TranClosure(T) \subseteq T  BY <2>tcTeq, <2>kc, <2>tcSS
  <2>sub2. T \subseteq TranClosure(T)  BY TranClosureExpanding
  <2> QED BY <2>sub1, <2>sub2
<1>tset. {z \in TranClosure(T) : B(z) = b} = {x}
  <2> SUFFICES ASSUME NEW z \in TranClosure(T), B(z) = b PROVE z = x  BY <1>tcT
  <2>zt. z \in T  BY <1>tcT
  <2>ach. \E q \in Tran(z) : IsProposal(q) /\ B(q) = b  BY <1>tmsgs, <2>zt, BAchievedByProposal
  <2> PICK q \in Tran(z) : IsProposal(q) /\ B(q) = b  BY <2>ach
  <2>kpcase. CASE z \in KP
    <3>qz. q = z \/ q \in TranExclusive(z)  BY DEF Tran, TranExclusive
    <3>xcase. CASE z = x  BY <3>xcase
    <3>kcase. CASE z \in known_messages[self]
      <4>1. q = z \/ q \in known_messages[self]
        <5>1. TranExclusive(z) \subseteq known_messages[self]
          BY <3>kcase, KnownTranClosureInvT DEF KnownTranClosureInvT, TranClosure, Tran
        <5> QED BY <3>qz, <5>1
      <4>2. CASE q = z  BY <4>2, <3>kcase
      <4>3. CASE q \in known_messages[self]  BY <4>3, <1>noneknown
      <4> QED BY <4>1, <4>2, <4>3
    <3> QED BY <3>xcase, <3>kcase, <2>kpcase
  <2>sscase. CASE z \in {mm \in Network : Sig(mm) = self}
    <3>notprop. ~IsProposal(z)
      <4>1. z \in Network /\ Sig(z) = self  BY <2>sscase
      <4> QED BY <4>1, SelfSentNotProposalInvT DEF SelfSentNotProposalInvT
    <3>qnz. q # z  BY <3>notprop
    <3>qte. q \in TranExclusive(z)  BY <3>qnz DEF Tran, TranExclusive
    <3>bound2. TranExclusive(z) \subseteq known_messages[self] \cup {mm \in Network : Sig(mm) = self}
      BY <2>sscase, SelfSentBoundedInvT DEF SelfSentBoundedInvT
    <3>qkorself. q \in known_messages[self] \/ q \in {mm \in Network : Sig(mm) = self}
      BY <3>qte, <3>bound2
    <3>qisprop. IsProposal(q)  OBVIOUS
    <3>notselfprop. q \notin {mm \in Network : Sig(mm) = self}
      <4> SUFFICES ASSUME q \in {mm \in Network : Sig(mm) = self} PROVE FALSE  OBVIOUS
      <4>1. q \in Network /\ Sig(q) = self  OBVIOUS
      <4> QED BY <4>1, <3>qisprop, SelfSentNotProposalInvT DEF SelfSentNotProposalInvT
    <3>qk. q \in known_messages[self]  BY <3>qkorself, <3>notselfprop
    <3>qbeqb. B(q) = b  OBVIOUS
    <3>qbneqb. B(q) # b  BY <3>qk, <1>noneknown
    <3> QED BY <3>qbeqb, <3>qbneqb
  <2>zdisj. z \in KP \/ z \in {mm \in Network : Sig(mm) = self}  BY <2>zt
  <2> QED BY <2>zdisj, <2>kpcase, <2>sscase
<1>ytc. TranExclusive(y) = T  OBVIOUS
<1>ynotprop. y \notin Proposals  OBVIOUS
<1>ybal. B(y) = b
  <2> DEFINE Cand == Proposals \cap Tran(y)
  <2>tranY. Tran(y) = {y} \cup T  BY <1>ytc DEF Tran, TranExclusive
  <2>candeq. Cand = Proposals \cap T
    <3>1. y \notin Proposals  BY <1>ynotprop
    <3> QED BY <2>tranY, <3>1
  <2>xincand. x \in Cand
    <3>a. x \in Proposals  BY DEF IsProposal
    <3>b. x \in T  OBVIOUS
    <3> QED BY <2>candeq, <3>a, <3>b
  <2>ubound. \A z \in Cand : ProposalBal(z) <= b
    <3> SUFFICES ASSUME NEW z \in Cand PROVE ProposalBal(z) <= b  OBVIOUS
    <3>1. z \in T  BY <2>candeq
    <3>2. IsProposal(z)  BY <2>candeq DEF IsProposal
    <3>3. z \in Messages  BY <3>1, <1>tmsgs
    <3>4. z \in GetProposals(z)
      <4>1. z \in Tran(z)  BY DEF Tran
      <4> QED BY <4>1, <2>candeq DEF GetProposals
    <3>5. ProposalBal(z) <= B(z)
      <4>fin. IsFiniteSet(GetProposals(z))
        <5>1. GetProposals(z) \subseteq Tran(z)  BY DEF GetProposals
        <5>2. IsFiniteSet(Tran(z))  BY <3>3, <1>mi DEF TranFinite
        <5> QED BY <5>1, <5>2, FS_Subset
      <4>sub. GetProposals(z) \subseteq Proposals  BY DEF GetProposals
      <4>ne. GetProposals(z) # {}  BY <3>4
      <4>choose. /\ B(z) \in {ProposalBal(w) : w \in GetProposals(z)}
                 /\ \A ww \in {ProposalBal(w) : w \in GetProposals(z)} : B(z) >= ww
        BY <4>fin, <4>sub, <4>ne, <1>mi, MaxBSetProperty DEF B
      <4>mem. ProposalBal(z) \in {ProposalBal(w) : w \in GetProposals(z)}  BY <3>4
      <4> QED BY <4>choose, <4>mem
    <3>6. B(z) <= b  BY <3>1, <1>tbound
    <3>7. ProposalBal(z) \in Ballots
      <4>1. MessageInterface.proposalbal \in [Proposals -> Ballots]  BY <1>mi DEF TypeOKMessageInterface
      <4>2. z \in Proposals  BY <3>2 DEF IsProposal
      <4> QED BY <4>1, <4>2 DEF ProposalBal
    <3>8. B(z) \in Ballots  BY <1>mi, <3>3, BBallot
    <3>9. b \in Ballots  OBVIOUS
    <3> QED BY <3>5, <3>6, <3>7, <3>8, <3>9, LeTransBallotsT
  <2>xbal. ProposalBal(x) = b  BY <1>xpropbal
  <2>candfin. IsFiniteSet(Cand)
    <3>ysub. Cand \subseteq Tran(y)  OBVIOUS
    <3>yfin. IsFiniteSet(Tran(y))  BY <1>mi DEF TranFinite
    <3> QED BY <3>ysub, <3>yfin, FS_Subset
  <2>candsub. Cand \subseteq Proposals  OBVIOUS
  <2>candne. Cand # {}  BY <2>xincand
  <2>ychoose. /\ B(y) \in {ProposalBal(w) : w \in Cand}
              /\ \A ww \in {ProposalBal(w) : w \in Cand} : B(y) >= ww
    BY <2>candfin, <2>candsub, <2>candne, <1>mi, MaxBSetProperty DEF B, GetProposals
  <2>yge. B(y) >= b
    <3>1. ProposalBal(x) \in {ProposalBal(w) : w \in Cand}  BY <2>xincand
    <3> QED BY <3>1, <2>ychoose, <2>xbal
  <2>yle. B(y) <= b
    <3>pw. PICK w \in Cand : B(y) = ProposalBal(w)  BY <2>ychoose
    <3> QED BY <3>pw, <2>ubound
  <2>yty. y \in Messages  OBVIOUS
  <2>ybalty. B(y) \in Ballots  BY <1>mi, <2>yty, BBallot
  <2>bty. b \in Ballots  OBVIOUS
  <2> QED BY <2>yge, <2>yle, <2>ybalty, <2>bty, EqFromLeGeBallotsT
<1>xney. x # y
  <2>xprop. x \in Proposals  BY DEF IsProposal
  <2> QED BY <2>xprop, <1>ynotprop
<1>yisoneb. IsOneB(y)
  <2>cardxy. {z \in Tran(y) : B(z) = b} = {x, y}
    <3>tranY. Tran(y) = {y} \cup T  BY <1>ytc DEF Tran, TranExclusive
    <3>seteq. {z \in T : B(z) = b} = {x}  BY <1>tset, <1>tcT
    <3> QED BY <3>tranY, <3>seteq, <1>ybal, <1>xney
  <2>card2. Cardinality({x, y}) = 2
    <3>1. IsFiniteSet({y})  BY FS_Singleton
    <3>2. Cardinality({y}) = 1  BY FS_Singleton
    <3>3. x \notin {y}  BY <1>xney
    <3>4. {x,y} = {x} \cup {y}  OBVIOUS
    <3> QED BY <3>1, <3>2, <3>3, <3>4, FS_AddElement
  <2> QED BY <2>cardxy, <2>card2, <1>ynotprop DEF IsOneB, IsProposal
<1> QED BY <1>ybal, <1>yisoneb

LEMMA OneBStepT ==
  MessageInterfaceAssumptions /\ LearnerGraphAssumptions /\
  Inv /\ KnownTranClosureInvT /\ SelfSentBoundedInvT /\ SelfSentNotProposalInvT /\
  SafeAcceptorChainInv /\ OneBInvariantT /\ [Next]_vars => OneBInvariantT'
<1> SUFFICES ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions,
                    Inv, KnownTranClosureInvT, SelfSentBoundedInvT, SelfSentNotProposalInvT,
                    SafeAcceptorChainInv, OneBInvariantT, [Next]_vars
             PROVE OneBInvariantT'  OBVIOUS
<1>i. /\ Network \in SUBSET Messages
      /\ known_messages \in [SafeAcceptors -> SUBSET Messages]
      /\ IsFiniteSet(Network)
      /\ (\A s \in SafeAcceptors : known_messages[s] \subseteq Network)
  BY DEF Inv
<1>2. CASE vars' = vars
  BY <1>2, OneBInvariantT DEF OneBInvariantT, vars
<1>3. CASE \E self \in SafeAcceptors \times Messages : safe_acceptor_receives_message(self)
  <2>1. PICK pp \in SafeAcceptors \times Messages : safe_acceptor_receives_message(pp)  BY <1>3
  <2> DEFINE self == pp[1]
  <2> DEFINE x == pp[2]
  <2>2. /\ x \in Network
        /\ TranExclusive(x) \subseteq known_messages[self]
        /\ known_messages' = [known_messages EXCEPT ![self] = known_messages[self] \cup {x}]
        /\ Network' = (LET T == (known_messages'[self] \cup {x})
                                  \cup {m \in Network : Sig(m) = self} IN
                       IF \E y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T
                         THEN Network \cup {CHOOSE y \in (Messages \ Proposals) :
                                             Sig(y) = self /\ TranExclusive(y) = T}
                         ELSE Network)
     BY <2>1 DEF safe_acceptor_receives_message
  <2>1a. self \in SafeAcceptors  BY <2>1
  <2>kself. known_messages'[self] = known_messages[self] \cup {x}  BY <2>2, <1>i, <2>1a
  <2>xmsg. x \in Messages  BY <2>2, <1>i
  <2> DEFINE T == (known_messages'[self] \cup {x}) \cup {m \in Network : Sig(m) = self}
  <2> DEFINE TU == (known_messages[self] \cup {x}) \cup {m \in Network : Sig(m) = self}
  <2>tueqt. TU = T  BY <2>kself
  <2>net. Network' = (IF \E y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T
                        THEN Network \cup {CHOOSE y \in (Messages \ Proposals) :
                                            Sig(y) = self /\ TranExclusive(y) = T}
                        ELSE Network)
     BY <2>2
  <2>netmono. Network \subseteq Network'  BY <2>net
  <2>knownmono. \A ss \in SafeAcceptors : known_messages[ss] \subseteq known_messages'[ss]
    BY <2>2, <1>i, <2>1a
  <2>invp. Inv'  BY InvStep
  <2>chainp. SafeAcceptorChainInv'  BY ChainStep
  <2>uncp2. self \notin CaughtS(Network')
    <3> SUFFICES ASSUME self \in CaughtS(Network') PROVE FALSE  OBVIOUS
    <3>3. \E m1 \in Network' : \E m2 \in Network' :
            Sig(m1) = self /\ Sig(m2) = self /\ m1 \notin Tran(m2) /\ m2 \notin Tran(m1)
      BY DEF CaughtS
    <3>4. PICK m1 \in Network' : \E m2 \in Network' :
            Sig(m1) = self /\ Sig(m2) = self /\ m1 \notin Tran(m2) /\ m2 \notin Tran(m1)
      BY <3>3
    <3>5. PICK m2 \in Network' :
            Sig(m1) = self /\ Sig(m2) = self /\ m1 \notin Tran(m2) /\ m2 \notin Tran(m1)
      BY <3>4
    <3>comp. m1 \in Tran(m2) \/ m2 \in Tran(m1)  BY <2>1a, <3>5, <2>chainp DEF SafeAcceptorChainInv
    <3> QED BY <3>comp, <3>5
  <2>tsub. T \subseteq Network'
    <3>1. known_messages'[self] \subseteq Network'  BY <2>invp DEF Inv
    <3>2. {m \in Network : Sig(m) = self} \subseteq Network  OBVIOUS
    <3>3. x \in known_messages'[self]  BY <2>kself
    <3> QED BY <3>1, <3>2, <3>3, <2>netmono
  <2>tcnet. TranClosure(T) \subseteq Network'
    <3> SUFFICES ASSUME NEW z \in TranClosure(T) PROVE z \in Network'  OBVIOUS
    <3>1. PICK w \in T : z \in Tran(w)  BY DEF TranClosure
    <3>2. w \in Network'  BY <3>1, <2>tsub
    <3>3. z = w \/ z \in TranExclusive(w)  BY <3>1 DEF Tran, TranExclusive
    <3>4. TranExclusive(w) \subseteq Network'  BY <3>2, <2>invp DEF Inv
    <3> QED BY <3>2, <3>3, <3>4
  <2>tuncaught. self \notin CaughtS(TranClosure(T))  BY <2>tcnet, <2>uncp2, CaughtSMonoT
  <2>tuncaughtU. self \notin CaughtS(TranClosure(TU))  BY <2>tuncaught, <2>tueqt
  <2> SUFFICES ASSUME NEW s \in SafeAcceptors, NEW b \in Ballots, NEW p \in known_messages'[s],
                      B(p) = b, IsProposal(p),
                      \A xx \in known_messages'[s] : IsProposal(xx) => B(xx) <= b
               PROVE \E oneb \in Network' : (B(oneb) = b /\ Sig(oneb) = s /\ IsOneB(oneb))
    BY DEF OneBInvariantT
  <2>scase. CASE s # self
    <3>keq. known_messages'[s] = known_messages[s]  BY <2>2, <2>scase, <1>i, <2>1a
    <3>pold. p \in known_messages[s]  BY <3>keq
    <3>bound. \A xx \in known_messages[s] : IsProposal(xx) => B(xx) <= b  BY <3>keq
    <3>old. \E oneb \in Network : (B(oneb) = b /\ Sig(oneb) = s /\ IsOneB(oneb))
      BY <3>pold, <3>bound, OneBInvariantT DEF OneBInvariantT
    <3> PICK oneb \in Network : B(oneb) = b /\ Sig(oneb) = s /\ IsOneB(oneb)  BY <3>old
    <3> QED BY <2>netmono
  <2>sceq. CASE s = self
    <3>oldcase. CASE p \in known_messages[self]
      <4>bound. \A xx \in known_messages[self] : IsProposal(xx) => B(xx) <= b
        BY <2>sceq, <2>kself
      <4>old. \E oneb \in Network : (B(oneb) = b /\ Sig(oneb) = self /\ IsOneB(oneb))
        BY <3>oldcase, <4>bound, OneBInvariantT DEF OneBInvariantT
      <4> PICK oneb \in Network : B(oneb) = b /\ Sig(oneb) = self /\ IsOneB(oneb)  BY <4>old
      <4> QED BY <2>netmono, <2>sceq
    <3>newcase. CASE p \notin known_messages[self]
      <4>pin. p \in known_messages'[self]  BY <2>sceq
      <4>peqx. p = x  BY <3>newcase, <2>kself, <4>pin
      <4>xprop. IsProposal(x)  BY <4>peqx
      <4>xbal. B(x) = b  BY <4>peqx
      <4>xnotknown. x \notin known_messages[self]  BY <3>newcase, <4>peqx
      <4>bound2. \A ww \in known_messages[self] : IsProposal(ww) => B(ww) <= b
        <5> SUFFICES ASSUME NEW ww \in known_messages[self], IsProposal(ww) PROVE B(ww) <= b  OBVIOUS
        <5>1. ww \in known_messages'[self]  BY <2>kself
        <5>2. ww \in known_messages'[s]  BY <5>1, <2>sceq
        <5> QED BY <5>2
      <4>knowbcase. CASE \E ww \in known_messages[self] : IsProposal(ww) /\ B(ww) = b
        <5> PICK ww \in known_messages[self] : IsProposal(ww) /\ B(ww) = b  BY <4>knowbcase
        <5>bound3. \A xx \in known_messages[self] : IsProposal(xx) => B(xx) <= b  BY <4>bound2
        <5>old. \E oneb \in Network : (B(oneb) = b /\ Sig(oneb) = self /\ IsOneB(oneb))
          BY <5>bound3, OneBInvariantT DEF OneBInvariantT
        <5> PICK oneb \in Network : B(oneb) = b /\ Sig(oneb) = self /\ IsOneB(oneb)  BY <5>old
        <5> QED BY <2>netmono, <2>sceq
      <4>notknowbcase. CASE ~(\E ww \in known_messages[self] : IsProposal(ww) /\ B(ww) = b)
        <5>nb. \A ww \in known_messages[self] : IsProposal(ww) => B(ww) # b  BY <4>notknowbcase
        <5>exU. \E y \in (Messages \ Proposals) :
                 /\ Sig(y) = self
                 /\ TranExclusive(y) = TU
                 /\ B(y) = b
                 /\ IsOneB(y)
          BY <2>1a, <2>2, <2>xmsg, <4>xprop, <4>xbal, <4>xnotknown, <5>nb, <4>bound2, <2>tuncaughtU,
             OneBConstructT
        <5>ex. \E y \in (Messages \ Proposals) :
                 /\ Sig(y) = self
                 /\ TranExclusive(y) = T
                 /\ B(y) = b
                 /\ IsOneB(y)
          BY <5>exU, <2>tueqt
        <5>ifcond. \E y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T
          BY <5>ex
        <5> DEFINE y0 == CHOOSE y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T
        <5>y0props. y0 \in (Messages \ Proposals) /\ Sig(y0) = self /\ TranExclusive(y0) = T
          BY <5>ifcond
        <5>y0propsU. y0 \in (Messages \ Proposals) /\ Sig(y0) = self /\ TranExclusive(y0) = TU
          BY <5>y0props, <2>tueqt
        <5>y0net. Network' = Network \cup {y0}  BY <2>net, <5>ifcond
        <5>y0in. y0 \in Network'  BY <5>y0net
        <5>y0any. B(y0) = b /\ IsOneB(y0)
          BY <2>1a, <2>2, <2>xmsg, <4>xprop, <4>xbal, <5>nb, <4>bound2, <5>y0propsU, OneBAnyWitnessT
        <5> QED BY <5>y0in, <5>y0props, <5>y0any, <2>sceq
      <4> QED BY <4>knowbcase, <4>notknowbcase
    <3> QED BY <3>oldcase, <3>newcase
  <2> QED BY <2>scase, <2>sceq
<1>4. CASE \E self \in ByzantineAcceptors : byz(self)
  <2>1. PICK self \in ByzantineAcceptors : byz(self)  BY <1>4
  <2>2. PICK y \in {z \in Messages : Sig(z) = self /\ TranExclusive(z) \subseteq Network} :
              Network' = (Network \cup {y})
     BY <2>1 DEF byz
  <2>k. known_messages' = known_messages  BY <2>1 DEF byz
  <2>netmono. Network \subseteq Network'  BY <2>2
  <2> SUFFICES ASSUME NEW s \in SafeAcceptors, NEW b \in Ballots, NEW p \in known_messages'[s],
                      B(p) = b, IsProposal(p),
                      \A xx \in known_messages'[s] : IsProposal(xx) => B(xx) <= b
               PROVE \E oneb \in Network' : (B(oneb) = b /\ Sig(oneb) = s /\ IsOneB(oneb))
    BY DEF OneBInvariantT
  <2>keq. known_messages'[s] = known_messages[s]  BY <2>k
  <2>pold. p \in known_messages[s]  BY <2>keq
  <2>bound. \A xx \in known_messages[s] : IsProposal(xx) => B(xx) <= b  BY <2>keq
  <2>old. \E oneb \in Network : (B(oneb) = b /\ Sig(oneb) = s /\ IsOneB(oneb))
    BY <2>pold, <2>bound, OneBInvariantT DEF OneBInvariantT
  <2> PICK oneb \in Network : B(oneb) = b /\ Sig(oneb) = s /\ IsOneB(oneb)  BY <2>old
  <2> QED BY <2>netmono
<1> QED BY <1>2, <1>3, <1>4 DEF Next

AuxT == Inv /\ KnownTranClosureInvT /\ SelfSentBoundedInvT /\ SelfSentNotProposalInvT /\
        SafeAcceptorChainInv

LEMMA InitAuxT == Init => AuxT
BY InitInv, InitKnownClosureT, InitSelfSentT, InitSelfSentNotProposalT, InitChain DEF AuxT

LEMMA AuxStepT == AuxT /\ [Next]_vars => AuxT'
<1> SUFFICES ASSUME AuxT, [Next]_vars PROVE AuxT'  OBVIOUS
<1>i. Inv /\ KnownTranClosureInvT /\ SelfSentBoundedInvT /\ SelfSentNotProposalInvT /\
      SafeAcceptorChainInv
  BY DEF AuxT
<1>a. Inv'  BY <1>i, InvStep
<1>b. KnownTranClosureInvT'  BY <1>i, KnownClosureStepT
<1>c. SelfSentBoundedInvT'  BY <1>i, SelfSentStepT
<1>d. SelfSentNotProposalInvT'  BY <1>i, SelfSentNotProposalStepT
<1>e. SafeAcceptorChainInv'  BY <1>i, ChainStep
<1> QED BY <1>a, <1>b, <1>c, <1>d, <1>e DEF AuxT

LEMMA AuxHoldsT == Spec => []AuxT
<1>1. Init => AuxT  BY InitAuxT
<1>2. AuxT /\ [Next]_vars => AuxT'  BY AuxStepT
<1> QED BY <1>1, <1>2, PTL DEF Spec

LEMMA OneBHoldsT ==
  (Spec /\ MessageInterfaceAssumptions /\ LearnerGraphAssumptions) => []OneBInvariantT
<1> SUFFICES ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions
             PROVE Spec => []OneBInvariantT  OBVIOUS
<1>1. Init => OneBInvariantT  BY InitOneBT
<1>2. AuxT /\ OneBInvariantT /\ [Next]_vars => OneBInvariantT'
  BY OneBStepT, MessageInterfaceAssumptions, LearnerGraphAssumptions DEF AuxT
<1>3. Spec => []AuxT  BY AuxHoldsT
<1> QED BY <1>1, <1>2, <1>3, PTL DEF Spec, AuxT

LEMMA OneBInvariantEqT == OneBInvariantT => OneBInvariant
BY DEF OneBInvariantT, OneBInvariant

LEMMA AlwaysOneBInvariant ==
  (/\ Spec
   /\ MessageInterfaceAssumptions
   /\ ValueInterfaceAssumptions
   /\ LearnerGraphAssumptions
  )=> []OneBInvariant
<1> SUFFICES ASSUME Spec, MessageInterfaceAssumptions, ValueInterfaceAssumptions, LearnerGraphAssumptions
             PROVE []OneBInvariant  OBVIOUS
<1>1. []OneBInvariantT  BY OneBHoldsT
<1> QED BY <1>1, OneBInvariantEqT, PTL
  
TwoAInvariantT ==
  \A s \in SafeAcceptors :
  \A b \in Ballots :
  \A alpha \in Learners :
  \A d \in (1..(MaxDepth(alpha))) :
  (/\ (\A xx \in known_messages[s] : (IsProposal(xx) => B(xx) <= b))
   /\ SigS({xx \in known_messages[s] :
           B(xx) = b /\ HasDepth(alpha, xx, d-1)}) \in Quorums(alpha)
  ) => \E twoa \in Network :
  (/\ B(twoa) = b
   /\ Sig(twoa) = s
   /\ HasDepth(alpha, twoa, d)
   /\ IsTwoA(twoa))

LEMMA InitTwoAT == LearnerGraphAssumptions /\ Init => TwoAInvariantT
<1> SUFFICES ASSUME LearnerGraphAssumptions, Init PROVE TwoAInvariantT  OBVIOUS
<1>lga. LearnersMightAgree /\ ValidLearnerGraphAssumption  BY DEF LearnerGraphAssumptions
<1>1. known_messages = [s \in SafeAcceptors |-> {}]  BY DEF Init
<1> SUFFICES ASSUME NEW s \in SafeAcceptors, NEW b \in Ballots, NEW alpha \in Learners,
                    NEW d \in (1..(MaxDepth(alpha))),
                    \A xx \in known_messages[s] : (IsProposal(xx) => B(xx) <= b),
                    SigS({xx \in known_messages[s] :
                          B(xx) = b /\ HasDepth(alpha, xx, d-1)}) \in Quorums(alpha)
             PROVE \E twoa \in Network :
                     B(twoa) = b /\ Sig(twoa) = s /\ HasDepth(alpha, twoa, d) /\ IsTwoA(twoa)
  BY DEF TwoAInvariantT
<1>2. known_messages[s] = {}  BY <1>1
<1>3. {xx \in known_messages[s] : B(xx) = b /\ HasDepth(alpha, xx, d-1)} = {}  BY <1>2
<1>4. SigS({}) = {}  BY DEF SigS
<1>5. SigS({xx \in known_messages[s] : B(xx) = b /\ HasDepth(alpha, xx, d-1)}) = {}
  BY <1>3, <1>4
<1>6. {} \in Quorums(alpha)  BY <1>5
<1>7. {} # {}  BY <1>lga, <1>6, QuorumsHaveMembers
<1> QED BY <1>7

LEMMA SigSFiniteT == ASSUME NEW S, IsFiniteSet(S) PROVE IsFiniteSet(SigS(S))
BY FS_Image DEF SigS

\* Isolated, freshly-named instantiation wrapper for AlwaysANewTwoA: avoids the
\* ambient "x" (the newly-learned message, in scope everywhere this gets used)
\* colliding with the axiom's own internally-bound "x", and keeps the
\* surrounding hypothesis context small enough for the backend to match.
LEMMA AlwaysANewTwoAInstT ==
  ASSUME MessageInterfaceAssumptions,
         NEW mm \in SUBSET Messages, NEW bb \in Ballots, NEW aa \in Acceptors,
         NEW alpha \in Learners, NEW dd \in (1..MaxDepth(alpha)),
         IsFiniteSet(mm), \A zz \in mm : B(zz) <= bb,
         aa \notin CaughtS(TranClosure(mm)),
         SigS({zz \in TranClosure(mm) : B(zz) = bb /\ HasDepth(alpha, zz, dd-1)}) \in Quorums(alpha)
  PROVE \E yy \in Messages :
          /\ (yy \in TranClosure(mm) \/ TranClosure(mm) = TranExclusive(yy))
          /\ B(yy) = bb
          /\ Sig(yy) = aa
          /\ HasDepth(alpha, yy, dd)
          /\ aa \notin Caught(yy)
          /\ IsTwoA(yy)
<1>ant. AlwaysANewTwoA  BY DEF MessageInterfaceAssumptions
<1> QED BY <1>ant DEF AlwaysANewTwoA

\* Companion to the (not-yet-written) TwoAConstructT: shows that ANY message y
\* satisfying Sig(y)=self /\ TranExclusive(y)=T necessarily has B(y)=b and
\* HasDepth(alpha,y,d) and IsTwoA(y) -- so it applies uniformly to whichever
\* witness the model's CHOOSE actually picks, exactly as OneBAnyWitnessT did
\* for OneB. Unlike OneB, no uniqueness ("only known ballot-b proposal") is
\* needed: Quorums are upward-closed (QuorumUpward), so a newly-learned x
\* contributing to the depth-(d-1) quorum only ever grows the quorum-signer
\* set, never breaks it.
LEMMA TwoAAnyWitnessT ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions,
         Inv, KnownTranClosureInvT, SelfSentBoundedInvT, SelfSentNotProposalInvT,
         NEW self \in SafeAcceptors, NEW x \in Messages, NEW b \in Ballots,
         NEW alpha \in Learners, NEW d \in (1..MaxDepth(alpha)),
         TranExclusive(x) \subseteq known_messages[self],
         B(x) = b, HasDepth(alpha, x, d-1),
         \A ww \in known_messages[self] : IsProposal(ww) => B(ww) <= b,
         SigS({xx \in (known_messages[self] \cup {x}) :
               B(xx) = b /\ HasDepth(alpha, xx, d-1)}) \in Quorums(alpha),
         NEW y \in (Messages \ Proposals),
         Sig(y) = self,
         TranExclusive(y) = (known_messages[self] \cup {x}) \cup {mm \in Network : Sig(mm) = self}
  PROVE B(y) = b /\ HasDepth(alpha, y, d) /\ IsTwoA(y)
<1>i. /\ Network \in SUBSET Messages
      /\ known_messages \in [SafeAcceptors -> SUBSET Messages]
      /\ IsFiniteSet(Network)
      /\ (\A s \in SafeAcceptors : known_messages[s] \subseteq Network)
  BY DEF Inv
<1>mi. TranFinite /\ TypeOKMessageInterface /\ AlwaysAProposal /\ TranTrans /\ TranAcyclic
  BY DEF MessageInterfaceAssumptions
<1>selfacc. self \in Acceptors  BY SafeAcceptorsSubsetAcceptors
<1> DEFINE KP == known_messages[self] \cup {x}
<1> DEFINE T == KP \cup {mm \in Network : Sig(mm) = self}
<1>kpmsgs. KP \subseteq Messages  BY <1>i
<1>tmsgs. T \subseteq Messages  BY <1>kpmsgs, <1>i
<1>ytc. TranExclusive(y) = T  OBVIOUS
<1>ynotprop. y \notin Proposals  OBVIOUS
<1>tbound. \A w \in T : B(w) <= b
  <2> SUFFICES ASSUME NEW w \in T PROVE B(w) <= b  OBVIOUS
  <2>wm. w \in Messages  BY <1>tmsgs
  <2>ach. \E q \in Tran(w) : IsProposal(q) /\ B(q) = B(w)  BY <2>wm, BAchievedByProposal
  <2> PICK q \in Tran(w) : IsProposal(q) /\ B(q) = B(w)  BY <2>ach
  <2>kpcase. CASE w \in KP
    <3>qw. q = w \/ q \in TranExclusive(w)  BY DEF Tran, TranExclusive
    <3>xcase. CASE w = x
      <4>1. B(w) = B(x)  BY <3>xcase
      <4>2. B(x) = b  OBVIOUS
      <4>3. B(w) = b  BY <4>1, <4>2
      <4>4. b \in Ballots  OBVIOUS
      <4>5. B(w) \in Ballots  BY <4>3, <4>4
      <4> QED BY <4>3, <4>4, <4>5, LeFromEqT
    <3>kcase. CASE w \in known_messages[self]
      <4>1. q = w \/ q \in known_messages[self]
        <5>1. TranExclusive(w) \subseteq known_messages[self]
          <6>a. Tran(w) \subseteq TranClosure(known_messages[self])  BY <3>kcase DEF TranClosure
          <6>b. TranClosure(known_messages[self]) = known_messages[self]
            BY KnownTranClosureInvT DEF KnownTranClosureInvT
          <6>c. TranExclusive(w) \subseteq Tran(w)  BY DEF Tran, TranExclusive
          <6> QED BY <6>a, <6>b, <6>c
        <5> QED BY <3>qw, <5>1
      <4>2. q \in known_messages[self]  BY <4>1, <3>kcase
      <4>3. IsProposal(q)  OBVIOUS
      <4>4. B(q) <= b  BY <4>2, <4>3
      <4>5. B(q) = B(w)  OBVIOUS
      <4> QED BY <4>4, <4>5
    <3> QED BY <3>xcase, <3>kcase, <2>kpcase
  <2>sscase. CASE w \in {mm \in Network : Sig(mm) = self}
    <3>notprop. ~IsProposal(w)
      <4>1. w \in Network /\ Sig(w) = self  BY <2>sscase
      <4> QED BY <4>1, SelfSentNotProposalInvT DEF SelfSentNotProposalInvT
    <3>qnw. q # w  BY <3>notprop
    <3>qte. q \in TranExclusive(w)  BY <3>qnw DEF Tran, TranExclusive
    <3>bound2. TranExclusive(w) \subseteq known_messages[self] \cup {mm \in Network : Sig(mm) = self}
      BY <2>sscase, SelfSentBoundedInvT DEF SelfSentBoundedInvT
    <3>qkorself. q \in known_messages[self] \/ q \in {mm \in Network : Sig(mm) = self}
      BY <3>qte, <3>bound2
    <3>qisprop. IsProposal(q)  OBVIOUS
    <3>notselfprop. q \notin {mm \in Network : Sig(mm) = self}
      <4> SUFFICES ASSUME q \in {mm \in Network : Sig(mm) = self} PROVE FALSE  OBVIOUS
      <4>1. q \in Network /\ Sig(q) = self  OBVIOUS
      <4> QED BY <4>1, <3>qisprop, SelfSentNotProposalInvT DEF SelfSentNotProposalInvT
    <3>qk. q \in known_messages[self]  BY <3>qkorself, <3>notselfprop
    <3>qbound. B(q) <= b  BY <3>qk, <3>qisprop
    <3>qbw. B(q) = B(w)  OBVIOUS
    <3> QED BY <3>qbound, <3>qbw
  <2> QED BY <2>kpcase, <2>sscase
<1>xachieve. \E q \in Tran(x) : IsProposal(q) /\ ProposalBal(q) = b /\ B(q) = b
  <2>ach. \E q \in Tran(x) : IsProposal(q) /\ ProposalBal(q) = B(x) /\ B(q) = B(x)  BY BAchievedByProposal
  <2> QED BY <2>ach
<1> PICK qx \in Tran(x) : IsProposal(qx) /\ ProposalBal(qx) = b /\ B(qx) = b  BY <1>xachieve
<1>qxT. qx \in T
  <2>1. Tran(x) \subseteq KP
    <3>a. x \in KP  OBVIOUS
    <3>b. TranExclusive(x) \subseteq KP  OBVIOUS
    <3>c. Tran(x) = {x} \cup TranExclusive(x)  BY DEF Tran, TranExclusive
    <3> QED BY <3>a, <3>b, <3>c
  <2> QED BY <2>1
<1>ybal. B(y) = b
  <2> DEFINE Cand == Proposals \cap Tran(y)
  <2>tranY. Tran(y) = {y} \cup T  BY <1>ytc DEF Tran, TranExclusive
  <2>candeq. Cand = Proposals \cap T
    <3>1. y \notin Proposals  BY <1>ynotprop
    <3> QED BY <2>tranY, <3>1
  <2>qxincand. qx \in Cand
    <3>a. qx \in Proposals  BY DEF IsProposal
    <3> QED BY <2>candeq, <3>a, <1>qxT
  <2>ubound. \A z \in Cand : ProposalBal(z) <= b
    <3> SUFFICES ASSUME NEW z \in Cand PROVE ProposalBal(z) <= b  OBVIOUS
    <3>1. z \in T  BY <2>candeq
    <3>2. IsProposal(z)  BY <2>candeq DEF IsProposal
    <3>3. z \in Messages  BY <3>1, <1>tmsgs
    <3>4. z \in GetProposals(z)
      <4>1. z \in Tran(z)  BY DEF Tran
      <4> QED BY <4>1, <2>candeq DEF GetProposals
    <3>5. ProposalBal(z) <= B(z)
      <4>fin. IsFiniteSet(GetProposals(z))
        <5>1. GetProposals(z) \subseteq Tran(z)  BY DEF GetProposals
        <5>2. IsFiniteSet(Tran(z))  BY <3>3, <1>mi DEF TranFinite
        <5> QED BY <5>1, <5>2, FS_Subset
      <4>sub. GetProposals(z) \subseteq Proposals  BY DEF GetProposals
      <4>ne. GetProposals(z) # {}  BY <3>4
      <4>choose. /\ B(z) \in {ProposalBal(w) : w \in GetProposals(z)}
                 /\ \A ww \in {ProposalBal(w) : w \in GetProposals(z)} : B(z) >= ww
        BY <4>fin, <4>sub, <4>ne, <1>mi, MaxBSetProperty DEF B
      <4>mem. ProposalBal(z) \in {ProposalBal(w) : w \in GetProposals(z)}  BY <3>4
      <4> QED BY <4>choose, <4>mem
    <3>6. B(z) <= b  BY <3>1, <1>tbound
    <3>7. ProposalBal(z) \in Ballots
      <4>1. MessageInterface.proposalbal \in [Proposals -> Ballots]  BY <1>mi DEF TypeOKMessageInterface
      <4>2. z \in Proposals  BY <3>2 DEF IsProposal
      <4> QED BY <4>1, <4>2 DEF ProposalBal
    <3>8. B(z) \in Ballots  BY <1>mi, <3>3, BBallot
    <3>9. b \in Ballots  OBVIOUS
    <3> QED BY <3>5, <3>6, <3>7, <3>8, <3>9, LeTransBallotsT
  <2>candfin. IsFiniteSet(Cand)
    <3>ysub. Cand \subseteq Tran(y)  OBVIOUS
    <3>yfin. IsFiniteSet(Tran(y))  BY <1>mi DEF TranFinite
    <3> QED BY <3>ysub, <3>yfin, FS_Subset
  <2>candsub. Cand \subseteq Proposals  OBVIOUS
  <2>candne. Cand # {}  BY <2>qxincand
  <2>ychoose. /\ B(y) \in {ProposalBal(w) : w \in Cand}
              /\ \A ww \in {ProposalBal(w) : w \in Cand} : B(y) >= ww
    BY <2>candfin, <2>candsub, <2>candne, <1>mi, MaxBSetProperty DEF B, GetProposals
  <2>yge. B(y) >= b
    <3>1. ProposalBal(qx) \in {ProposalBal(w) : w \in Cand}  BY <2>qxincand
    <3> QED BY <3>1, <2>ychoose
  <2>yle. B(y) <= b
    <3>pw. PICK w \in Cand : B(y) = ProposalBal(w)  BY <2>ychoose
    <3> QED BY <3>pw, <2>ubound
  <2>yty. y \in Messages  OBVIOUS
  <2>ybalty. B(y) \in Ballots  BY <1>mi, <2>yty, BBallot
  <2>bty. b \in Ballots  OBVIOUS
  <2> QED BY <2>yge, <2>yle, <2>ybalty, <2>bty, EqFromLeGeBallotsT
<1>qdeq. {q \in TranExclusive(y) : B(y) = B(q) /\ HasDepth(alpha, q, d-1)}
           = {xx \in T : B(xx) = b /\ HasDepth(alpha, xx, d-1)}
  BY <1>ytc, <1>ybal
<1>dpos. d >= 1  OBVIOUS
<1>qdval. Qd(alpha, y, d) = {xx \in T : B(xx) = b /\ HasDepth(alpha, xx, d-1)}
  BY <1>dpos, <1>qdeq DEF Qd
<1>subKPT. {xx \in KP : B(xx) = b /\ HasDepth(alpha, xx, d-1)}
             \subseteq {xx \in T : B(xx) = b /\ HasDepth(alpha, xx, d-1)}
  OBVIOUS
<1>sigsub. SigS({xx \in KP : B(xx) = b /\ HasDepth(alpha, xx, d-1)})
             \subseteq SigS(Qd(alpha, y, d))
  BY <1>subKPT, <1>qdval DEF SigS
<1>qdfin. IsFiniteSet(Qd(alpha, y, d))
  <2>1. Qd(alpha, y, d) \subseteq T  BY <1>qdval
  <2>2. IsFiniteSet(T)
    <3>0. known_messages[self] \subseteq Network  BY <1>i
    <3>0b. IsFiniteSet(known_messages[self])  BY <3>0, <1>i, FS_Subset
    <3>1. IsFiniteSet(KP)  BY <3>0b, FS_AddElement
    <3>2. IsFiniteSet({mm \in Network : Sig(mm) = self})  BY <1>i, FS_Subset
    <3> QED BY <3>1, <3>2, FS_Union
  <2> QED BY <2>1, <2>2, FS_Subset
<1>sigfin. IsFiniteSet(SigS(Qd(alpha, y, d)))  BY <1>qdfin, FS_Image DEF SigS
<1>sigacc. SigS(Qd(alpha, y, d)) \subseteq Acceptors
  <2> SUFFICES ASSUME NEW aa \in SigS(Qd(alpha, y, d)) PROVE aa \in Acceptors  OBVIOUS
  <2>1. PICK q \in Qd(alpha, y, d) : aa = Sig(q)  BY DEF SigS
  <2>2. HasDepth(alpha, q, d-1)  BY <2>1, <1>qdval
  <2>3. Sig(q) \in Acceptors  BY <2>2 DEF HasDepth
  <2> QED BY <2>1, <2>3
<1>quo. SigS(Qd(alpha, y, d)) \in Quorums(alpha)
  BY <1>sigsub, <1>sigfin, <1>sigacc, QuorumUpward
<1>hd. HasDepth(alpha, y, d)
  <2>ysig. Sig(y) \in Acceptors  BY <1>selfacc
  <2>hddef. HasDepth(alpha, y, d) =
              (/\ Sig(y) \in Acceptors
               /\ IF d = 0 THEN (IsOneB(y) /\ Fresh(alpha, y))
                           ELSE SigS(Qd(alpha, y, d)) \in Quorums(alpha))
    BY <1>mi, HasDepthDef
  <2>dne0. d # 0  BY <1>dpos
  <2> QED BY <2>ysig, <2>hddef, <2>dne0, <1>quo
<1>hd1. HasDepth(alpha, y, 1)
  <2>lga. LearnersMightAgree /\ ValidLearnerGraphAssumption  BY DEF LearnerGraphAssumptions
  <2> QED BY <1>mi, <2>lga, <1>hd, <1>dpos, HasDepthDownward
<1>istwoa. IsTwoA(y)
  <2>1. ~IsProposal(y)  BY <1>ynotprop DEF IsProposal
  <2> QED BY <2>1, <1>hd1 DEF IsTwoA
<1> QED BY <1>ybal, <1>hd, <1>istwoa

\* Core construction: within a learn step where self learns x contributing to
\* a depth-(d-1) quorum for (b,alpha) that newly becomes satisfied, the
\* forced-send mechanism's target set T is provably a valid AlwaysANewTwoA
\* input, giving a witness x2 -- either already inside T (so already in
\* Network', no forced-send needed) or a fresh message with TranExclusive
\* exactly T (needing TwoAAnyWitnessT to handle whichever witness CHOOSE picks).
LEMMA TwoAConstructT ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions,
         Inv, KnownTranClosureInvT, SelfSentBoundedInvT, SelfSentNotProposalInvT,
         NEW self \in SafeAcceptors, NEW x \in Messages, NEW b \in Ballots,
         NEW alpha \in Learners, NEW d \in (1..MaxDepth(alpha)),
         TranExclusive(x) \subseteq known_messages[self],
         B(x) = b, HasDepth(alpha, x, d-1),
         \A ww \in known_messages[self] : IsProposal(ww) => B(ww) <= b,
         SigS({xx \in (known_messages[self] \cup {x}) :
               B(xx) = b /\ HasDepth(alpha, xx, d-1)}) \in Quorums(alpha),
         self \notin CaughtS(TranClosure((known_messages[self] \cup {x})
                                          \cup {mm \in Network : Sig(mm) = self}))
  PROVE \E x2 \in Messages :
          /\ (x2 \in ((known_messages[self] \cup {x}) \cup {mm \in Network : Sig(mm) = self})
              \/ TranExclusive(x2) = ((known_messages[self] \cup {x}) \cup {mm \in Network : Sig(mm) = self}))
          /\ B(x2) = b
          /\ Sig(x2) = self
          /\ HasDepth(alpha, x2, d)
          /\ self \notin Caught(x2)
          /\ IsTwoA(x2)
<1>i. /\ Network \in SUBSET Messages
      /\ known_messages \in [SafeAcceptors -> SUBSET Messages]
      /\ IsFiniteSet(Network)
      /\ (\A s \in SafeAcceptors : known_messages[s] \subseteq Network)
  BY DEF Inv
<1>mi. TranFinite /\ TypeOKMessageInterface /\ AlwaysAProposal /\ TranTrans /\ TranAcyclic /\ AlwaysANewTwoA
  BY DEF MessageInterfaceAssumptions
<1>selfacc. self \in Acceptors  BY SafeAcceptorsSubsetAcceptors
<1> DEFINE KP == known_messages[self] \cup {x}
<1> DEFINE T == KP \cup {mm \in Network : Sig(mm) = self}
<1>kpmsgs. KP \subseteq Messages  BY <1>i
<1>tmsgs. T \subseteq Messages  BY <1>kpmsgs, <1>i
<1>tfin. IsFiniteSet(T)
  <2>0. known_messages[self] \subseteq Network  BY <1>i
  <2>0b. IsFiniteSet(known_messages[self])  BY <2>0, <1>i, FS_Subset
  <2>1. IsFiniteSet(KP)  BY <2>0b, FS_AddElement
  <2>2. IsFiniteSet({mm \in Network : Sig(mm) = self})  BY <1>i, FS_Subset
  <2> QED BY <2>1, <2>2, FS_Union
<1>tbound. \A w \in T : B(w) <= b
  <2> SUFFICES ASSUME NEW w \in T PROVE B(w) <= b  OBVIOUS
  <2>wm. w \in Messages  BY <1>tmsgs
  <2>ach. \E q \in Tran(w) : IsProposal(q) /\ B(q) = B(w)  BY <2>wm, BAchievedByProposal
  <2> PICK q \in Tran(w) : IsProposal(q) /\ B(q) = B(w)  BY <2>ach
  <2>kpcase. CASE w \in KP
    <3>qw. q = w \/ q \in TranExclusive(w)  BY DEF Tran, TranExclusive
    <3>xcase. CASE w = x
      <4>1. B(w) = B(x)  BY <3>xcase
      <4>2. B(x) = b  OBVIOUS
      <4>3. B(w) = b  BY <4>1, <4>2
      <4>4. b \in Ballots  OBVIOUS
      <4>5. B(w) \in Ballots  BY <4>3, <4>4
      <4> QED BY <4>3, <4>4, <4>5, LeFromEqT
    <3>kcase. CASE w \in known_messages[self]
      <4>1. q = w \/ q \in known_messages[self]
        <5>1. TranExclusive(w) \subseteq known_messages[self]
          <6>a. Tran(w) \subseteq TranClosure(known_messages[self])  BY <3>kcase DEF TranClosure
          <6>b. TranClosure(known_messages[self]) = known_messages[self]
            BY KnownTranClosureInvT DEF KnownTranClosureInvT
          <6>c. TranExclusive(w) \subseteq Tran(w)  BY DEF Tran, TranExclusive
          <6> QED BY <6>a, <6>b, <6>c
        <5> QED BY <3>qw, <5>1
      <4>2. q \in known_messages[self]  BY <4>1, <3>kcase
      <4>3. IsProposal(q)  OBVIOUS
      <4>4. B(q) <= b  BY <4>2, <4>3
      <4>5. B(q) = B(w)  OBVIOUS
      <4> QED BY <4>4, <4>5
    <3> QED BY <3>xcase, <3>kcase, <2>kpcase
  <2>sscase. CASE w \in {mm \in Network : Sig(mm) = self}
    <3>notprop. ~IsProposal(w)
      <4>1. w \in Network /\ Sig(w) = self  BY <2>sscase
      <4> QED BY <4>1, SelfSentNotProposalInvT DEF SelfSentNotProposalInvT
    <3>qnw. q # w  BY <3>notprop
    <3>qte. q \in TranExclusive(w)  BY <3>qnw DEF Tran, TranExclusive
    <3>bound2. TranExclusive(w) \subseteq known_messages[self] \cup {mm \in Network : Sig(mm) = self}
      BY <2>sscase, SelfSentBoundedInvT DEF SelfSentBoundedInvT
    <3>qkorself. q \in known_messages[self] \/ q \in {mm \in Network : Sig(mm) = self}
      BY <3>qte, <3>bound2
    <3>qisprop. IsProposal(q)  OBVIOUS
    <3>notselfprop. q \notin {mm \in Network : Sig(mm) = self}
      <4> SUFFICES ASSUME q \in {mm \in Network : Sig(mm) = self} PROVE FALSE  OBVIOUS
      <4>1. q \in Network /\ Sig(q) = self  OBVIOUS
      <4> QED BY <4>1, <3>qisprop, SelfSentNotProposalInvT DEF SelfSentNotProposalInvT
    <3>qk. q \in known_messages[self]  BY <3>qkorself, <3>notselfprop
    <3>qbound. B(q) <= b  BY <3>qk, <3>qisprop
    <3>qbw. B(q) = B(w)  OBVIOUS
    <3> QED BY <3>qbound, <3>qbw
  <2> QED BY <2>kpcase, <2>sscase
<1>tcT. TranClosure(T) = T
  <2>kc. TranClosure(KP) = KP
    <3>1. TranClosure(known_messages[self]) = known_messages[self]
      BY KnownTranClosureInvT DEF KnownTranClosureInvT
    <3>2. TranClosure({x}) = Tran(x)  BY TranClosureSingleton
    <3>3. TranClosure(KP) = TranClosure(known_messages[self]) \cup TranClosure({x})  BY TranClosureUnion
    <3>4. TranExclusive(x) \subseteq KP  OBVIOUS
    <3>5. Tran(x) \subseteq KP
      <4>a. x \in KP  OBVIOUS
      <4>b. Tran(x) = {x} \cup TranExclusive(x)  BY DEF Tran, TranExclusive
      <4> QED BY <3>4, <4>a, <4>b
    <3> QED BY <3>1, <3>2, <3>3, <3>5, TranClosureExpanding
  <2>ssb. \A z \in Network :
            Sig(z) = self => TranExclusive(z) \subseteq KP \cup {mm \in Network : Sig(mm) = self}
    <3> SUFFICES ASSUME NEW z \in Network, Sig(z) = self
                 PROVE TranExclusive(z) \subseteq KP \cup {mm \in Network : Sig(mm) = self}  OBVIOUS
    <3>1. TranExclusive(z) \subseteq known_messages[self] \cup {mm \in Network : Sig(mm) = self}
      BY SelfSentBoundedInvT DEF SelfSentBoundedInvT
    <3> QED BY <3>1
  <2>tcSS. TranClosure({mm \in Network : Sig(mm) = self}) \subseteq T
    <3> SUFFICES ASSUME NEW z \in TranClosure({mm \in Network : Sig(mm) = self}) PROVE z \in T  OBVIOUS
    <3>1. PICK w \in {mm \in Network : Sig(mm) = self} : z \in Tran(w)  BY DEF TranClosure
    <3>2. z = w \/ z \in TranExclusive(w)  BY <3>1 DEF Tran, TranExclusive
    <3>3. w \in Network /\ Sig(w) = self  BY <3>1
    <3>4. TranExclusive(w) \subseteq KP \cup {mm \in Network : Sig(mm) = self}  BY <3>3, <2>ssb
    <3> QED BY <3>1, <3>2, <3>4
  <2>tcTeq. TranClosure(T) = TranClosure(KP) \cup TranClosure({mm \in Network : Sig(mm) = self})
    BY TranClosureUnion
  <2>sub1. TranClosure(T) \subseteq T  BY <2>tcTeq, <2>kc, <2>tcSS
  <2>sub2. T \subseteq TranClosure(T)  BY TranClosureExpanding
  <2> QED BY <2>sub1, <2>sub2
<1> DEFINE FiltKP == {xx \in KP : B(xx) = b /\ HasDepth(alpha, xx, d-1)}
<1> DEFINE FiltT == {xx \in T : B(xx) = b /\ HasDepth(alpha, xx, d-1)}
<1>quoT. SigS(FiltT) \in Quorums(alpha)
  <2>sub. FiltKP \subseteq FiltT  OBVIOUS
  <2>sigsub. SigS(FiltKP) \subseteq SigS(FiltT)  BY <2>sub DEF SigS
  <2>tfilt. FiltT \subseteq T  OBVIOUS
  <2>fin. IsFiniteSet(FiltT)  BY <2>tfilt, <1>tfin, FS_Subset
  <2>sigfin. IsFiniteSet(SigS(FiltT))  BY <2>fin, SigSFiniteT
  <2>acc. SigS(FiltT) \subseteq Acceptors
    <3> SUFFICES ASSUME NEW aa \in SigS(FiltT) PROVE aa \in Acceptors  OBVIOUS
    <3>1. PICK qq \in FiltT : aa = Sig(qq)  BY DEF SigS
    <3>2. HasDepth(alpha, qq, d-1)  BY <3>1
    <3>3. Sig(qq) \in Acceptors  BY <3>2 DEF HasDepth
    <3> QED BY <3>1, <3>3
  <2>quoKP. SigS(FiltKP) \in Quorums(alpha)  OBVIOUS
  <2> QED BY <2>quoKP, <2>sigsub, <2>sigfin, <2>acc, QuorumUpward, <1>tcT
<1>uncaughtT. self \notin CaughtS(TranClosure(T))  OBVIOUS
<1>tinSM. T \in SUBSET Messages  BY <1>tmsgs
<1>dtyp. d \in (1..MaxDepth(alpha))  OBVIOUS
<1>anhyps. /\ self \in Acceptors
          /\ T \in SUBSET Messages
          /\ d \in (1..MaxDepth(alpha))
          /\ IsFiniteSet(T)
          /\ (\A ww \in T : B(ww) <= b)
          /\ SigS({xx \in TranClosure(T) : B(xx) = b /\ HasDepth(alpha, xx, d-1)}) \in Quorums(alpha)
          /\ self \notin CaughtS(TranClosure(T))
  BY <1>selfacc, <1>tinSM, <1>dtyp, <1>tfin, <1>tbound, <1>quoT, <1>uncaughtT, <1>tcT
<1>anb. \E x2 \in Messages :
          /\ (x2 \in TranClosure(T) \/ TranClosure(T) = TranExclusive(x2))
          /\ B(x2) = b
          /\ Sig(x2) = self
          /\ HasDepth(alpha, x2, d)
          /\ self \notin Caught(x2)
          /\ IsTwoA(x2)
  BY <1>anhyps, MessageInterfaceAssumptions, AlwaysANewTwoAInstT
<1> PICK x2 \in Messages :
      /\ (x2 \in TranClosure(T) \/ TranClosure(T) = TranExclusive(x2))
      /\ B(x2) = b
      /\ Sig(x2) = self
      /\ HasDepth(alpha, x2, d)
      /\ self \notin Caught(x2)
      /\ IsTwoA(x2)
  BY <1>anb
<1>disj. x2 \in T \/ TranExclusive(x2) = T  BY <1>tcT
<1> QED BY <1>disj

LEMMA TwoAStepT ==
  MessageInterfaceAssumptions /\ LearnerGraphAssumptions /\
  Inv /\ KnownTranClosureInvT /\ SelfSentBoundedInvT /\ SelfSentNotProposalInvT /\
  SafeAcceptorChainInv /\ TwoAInvariantT /\ [Next]_vars => TwoAInvariantT'
<1> SUFFICES ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions,
                    Inv, KnownTranClosureInvT, SelfSentBoundedInvT, SelfSentNotProposalInvT,
                    SafeAcceptorChainInv, TwoAInvariantT, [Next]_vars
             PROVE TwoAInvariantT'  OBVIOUS
<1>i. /\ Network \in SUBSET Messages
      /\ known_messages \in [SafeAcceptors -> SUBSET Messages]
      /\ IsFiniteSet(Network)
      /\ (\A s \in SafeAcceptors : known_messages[s] \subseteq Network)
  BY DEF Inv
<1>2. CASE vars' = vars
  BY <1>2, TwoAInvariantT DEF TwoAInvariantT, vars
<1>3. CASE \E self \in SafeAcceptors \times Messages : safe_acceptor_receives_message(self)
  <2>1. PICK pp \in SafeAcceptors \times Messages : safe_acceptor_receives_message(pp)  BY <1>3
  <2> DEFINE self == pp[1]
  <2> DEFINE x == pp[2]
  <2>2. /\ x \in Network
        /\ TranExclusive(x) \subseteq known_messages[self]
        /\ known_messages' = [known_messages EXCEPT ![self] = known_messages[self] \cup {x}]
        /\ Network' = (LET T == (known_messages'[self] \cup {x})
                                  \cup {m \in Network : Sig(m) = self} IN
                       IF \E y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T
                         THEN Network \cup {CHOOSE y \in (Messages \ Proposals) :
                                             Sig(y) = self /\ TranExclusive(y) = T}
                         ELSE Network)
     BY <2>1 DEF safe_acceptor_receives_message
  <2>1a. self \in SafeAcceptors  BY <2>1
  <2>kself. known_messages'[self] = known_messages[self] \cup {x}  BY <2>2, <1>i, <2>1a
  <2>xmsg. x \in Messages  BY <2>2, <1>i
  <2>xte. TranExclusive(x) \subseteq known_messages[self]  BY <2>2
  <2> DEFINE T == (known_messages'[self] \cup {x}) \cup {m \in Network : Sig(m) = self}
  <2> DEFINE TU == (known_messages[self] \cup {x}) \cup {m \in Network : Sig(m) = self}
  <2>tueqt. TU = T  BY <2>kself
  <2>net. Network' = (IF \E y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T
                        THEN Network \cup {CHOOSE y \in (Messages \ Proposals) :
                                            Sig(y) = self /\ TranExclusive(y) = T}
                        ELSE Network)
     BY <2>2
  <2>netmono. Network \subseteq Network'  BY <2>net
  <2>knownmono. \A ss \in SafeAcceptors : known_messages[ss] \subseteq known_messages'[ss]
    BY <2>2, <1>i, <2>1a
  <2>invp. Inv'  BY InvStep
  <2>chainp. SafeAcceptorChainInv'  BY ChainStep
  <2>uncp2. self \notin CaughtS(Network')
    <3> SUFFICES ASSUME self \in CaughtS(Network') PROVE FALSE  OBVIOUS
    <3>3. \E m1 \in Network' : \E m2 \in Network' :
            Sig(m1) = self /\ Sig(m2) = self /\ m1 \notin Tran(m2) /\ m2 \notin Tran(m1)
      BY DEF CaughtS
    <3>4. PICK m1 \in Network' : \E m2 \in Network' :
            Sig(m1) = self /\ Sig(m2) = self /\ m1 \notin Tran(m2) /\ m2 \notin Tran(m1)
      BY <3>3
    <3>5. PICK m2 \in Network' :
            Sig(m1) = self /\ Sig(m2) = self /\ m1 \notin Tran(m2) /\ m2 \notin Tran(m1)
      BY <3>4
    <3>comp. m1 \in Tran(m2) \/ m2 \in Tran(m1)  BY <2>1a, <3>5, <2>chainp DEF SafeAcceptorChainInv
    <3> QED BY <3>comp, <3>5
  <2>tsub. TU \subseteq Network'
    <3>1. known_messages'[self] \subseteq Network'  BY <2>invp DEF Inv
    <3>2. {m \in Network : Sig(m) = self} \subseteq Network  OBVIOUS
    <3>3. x \in known_messages'[self]  BY <2>kself
    <3>4. known_messages[self] \subseteq known_messages'[self]  BY <2>kself
    <3>5. known_messages[self] \subseteq Network'  BY <3>4, <3>1
    <3> QED BY <3>1, <3>2, <3>3, <3>5, <2>netmono
  <2>tcnet. TranClosure(TU) \subseteq Network'
    <3> SUFFICES ASSUME NEW z \in TranClosure(TU) PROVE z \in Network'  OBVIOUS
    <3>1. PICK w \in TU : z \in Tran(w)  BY DEF TranClosure
    <3>2. w \in Network'  BY <3>1, <2>tsub
    <3>3. z = w \/ z \in TranExclusive(w)  BY <3>1 DEF Tran, TranExclusive
    <3>4. TranExclusive(w) \subseteq Network'  BY <3>2, <2>invp DEF Inv
    <3> QED BY <3>2, <3>3, <3>4
  <2>tuncaughtU. self \notin CaughtS(TranClosure(TU))  BY <2>tcnet, <2>uncp2, CaughtSMonoT
  <2> SUFFICES ASSUME NEW s \in SafeAcceptors, NEW b \in Ballots, NEW alpha \in Learners,
                      NEW d \in (1..MaxDepth(alpha)),
                      \A xx \in known_messages'[s] : (IsProposal(xx) => B(xx) <= b),
                      SigS({xx \in known_messages'[s] :
                            B(xx) = b /\ HasDepth(alpha, xx, d-1)}) \in Quorums(alpha)
               PROVE \E twoa \in Network' :
                       B(twoa) = b /\ Sig(twoa) = s /\ HasDepth(alpha, twoa, d) /\ IsTwoA(twoa)
    BY DEF TwoAInvariantT
  <2>scase. CASE s # self
    <3>keq. known_messages'[s] = known_messages[s]  BY <2>2, <2>scase, <1>i, <2>1a
    <3>bound. \A xx \in known_messages[s] : (IsProposal(xx) => B(xx) <= b)  BY <3>keq
    <3>quo. SigS({xx \in known_messages[s] : B(xx) = b /\ HasDepth(alpha, xx, d-1)}) \in Quorums(alpha)
      BY <3>keq
    <3>old. \E twoa \in Network : B(twoa) = b /\ Sig(twoa) = s /\ HasDepth(alpha, twoa, d) /\ IsTwoA(twoa)
      BY <3>bound, <3>quo, TwoAInvariantT DEF TwoAInvariantT
    <3> PICK twoa \in Network : B(twoa) = b /\ Sig(twoa) = s /\ HasDepth(alpha, twoa, d) /\ IsTwoA(twoa)
      BY <3>old
    <3> QED BY <2>netmono
  <2>sceq. CASE s = self
    <3>bound2. \A ww \in known_messages[self] : IsProposal(ww) => B(ww) <= b
      <4> SUFFICES ASSUME NEW ww \in known_messages[self], IsProposal(ww) PROVE B(ww) <= b  OBVIOUS
      <4>1. ww \in known_messages'[self]  BY <2>kself
      <4>2. ww \in known_messages'[s]  BY <4>1, <2>sceq
      <4> QED BY <4>2
    <3>contribcase. CASE B(x) = b /\ HasDepth(alpha, x, d-1)
      <4>quoKPpre. SigS({xx \in (known_messages[self] \cup {x}) :
                         B(xx) = b /\ HasDepth(alpha, xx, d-1)}) \in Quorums(alpha)
        <5>1. known_messages[self] \cup {x} = known_messages'[s]  BY <2>kself, <2>sceq
        <5> QED BY <5>1
      <4>ex. \E x2 \in Messages :
               /\ (x2 \in TU \/ TranExclusive(x2) = TU)
               /\ B(x2) = b
               /\ Sig(x2) = self
               /\ HasDepth(alpha, x2, d)
               /\ self \notin Caught(x2)
               /\ IsTwoA(x2)
        BY <2>1a, <2>xmsg, <2>xte, <3>contribcase, <4>quoKPpre, <3>bound2, <2>tuncaughtU,
           MessageInterfaceAssumptions, LearnerGraphAssumptions, TwoAConstructT
      <4> PICK x2 \in Messages :
            /\ (x2 \in TU \/ TranExclusive(x2) = TU)
            /\ B(x2) = b
            /\ Sig(x2) = self
            /\ HasDepth(alpha, x2, d)
            /\ self \notin Caught(x2)
            /\ IsTwoA(x2)
        BY <4>ex
      <4>case1. CASE x2 \in TU
        <5>x2net. x2 \in Network'  BY <4>case1, <2>tsub
        <5> QED BY <5>x2net, <2>sceq
      <4>case2. CASE TranExclusive(x2) = TU
        <5>tex2t. TranExclusive(x2) = T  BY <4>case2, <2>tueqt
        <5>x2notprop. x2 \notin Proposals  BY DEF IsTwoA, IsProposal
        <5>ifcond. \E y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T
          BY <5>tex2t, <5>x2notprop
        <5> DEFINE y0 == CHOOSE y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T
        <5>y0props. y0 \in (Messages \ Proposals) /\ Sig(y0) = self /\ TranExclusive(y0) = T
          BY <5>ifcond
        <5>y0propsU. y0 \in (Messages \ Proposals) /\ Sig(y0) = self /\ TranExclusive(y0) = TU
          BY <5>y0props, <2>tueqt
        <5>y0net. Network' = Network \cup {y0}  BY <2>net, <5>ifcond
        <5>y0in. y0 \in Network'  BY <5>y0net
        \* Inlined (rather than cited) copy of TwoAAnyWitnessT's proof, substituting
        \* y0 for y and TU for its internal T: repeated attempts to cite
        \* TwoAAnyWitnessT directly from this deeply-nested nine-hypothesis call
        \* site failed for the backend regardless of how the hypotheses were
        \* packaged, so we fall back to the reliable inlined form.
        <5>mi. TranFinite /\ TypeOKMessageInterface /\ AlwaysAProposal /\ TranTrans /\ TranAcyclic
          BY DEF MessageInterfaceAssumptions
        <5>KPT. TranExclusive(y0) = TU  BY <5>y0propsU
        <5>ynotprop. y0 \notin Proposals  BY <5>y0propsU
        <5>y0msg. y0 \in Messages  BY <5>y0propsU
        <5>y0sig. Sig(y0) = self  BY <5>y0propsU
        <5>tbound2. \A w \in TU : B(w) <= b
          <6> SUFFICES ASSUME NEW w \in TU PROVE B(w) <= b  OBVIOUS
          <6>wm. w \in Messages  BY <2>xte, <2>xmsg, <1>i
          <6>ach. \E q \in Tran(w) : IsProposal(q) /\ B(q) = B(w)  BY <6>wm, BAchievedByProposal
          <6> PICK q \in Tran(w) : IsProposal(q) /\ B(q) = B(w)  BY <6>ach
          <6>kpcase. CASE w \in (known_messages[self] \cup {x})
            <7>qw. q = w \/ q \in TranExclusive(w)  BY DEF Tran, TranExclusive
            <7>xcase. CASE w = x
              <8>1. B(w) = B(x)  BY <7>xcase
              <8>2. B(x) = b  BY <3>contribcase
              <8>3. B(w) = b  BY <8>1, <8>2
              <8>4. b \in Ballots  OBVIOUS
              <8>5. B(w) \in Ballots  BY <8>3, <8>4
              <8> QED BY <8>3, <8>4, <8>5, LeFromEqT
            <7>kcase. CASE w \in known_messages[self]
              <8>1. q = w \/ q \in known_messages[self]
                <9>1. TranExclusive(w) \subseteq known_messages[self]
                  <10>a. Tran(w) \subseteq TranClosure(known_messages[self])  BY <7>kcase DEF TranClosure
                  <10>b. TranClosure(known_messages[self]) = known_messages[self]
                    BY KnownTranClosureInvT DEF KnownTranClosureInvT
                  <10>c. TranExclusive(w) \subseteq Tran(w)  BY DEF Tran, TranExclusive
                  <10> QED BY <10>a, <10>b, <10>c
                <9> QED BY <7>qw, <9>1
              <8>2. q \in known_messages[self]  BY <8>1, <7>kcase
              <8>3. IsProposal(q)  OBVIOUS
              <8>4. B(q) <= b  BY <8>2, <8>3, <3>bound2
              <8>5. B(q) = B(w)  OBVIOUS
              <8> QED BY <8>4, <8>5
            <7> QED BY <7>xcase, <7>kcase, <6>kpcase
          <6>sscase. CASE w \in {mm \in Network : Sig(mm) = self}
            <7>notprop. ~IsProposal(w)
              <8>1. w \in Network /\ Sig(w) = self  BY <6>sscase
              <8> QED BY <8>1, SelfSentNotProposalInvT DEF SelfSentNotProposalInvT
            <7>qnw. q # w  BY <7>notprop
            <7>qte. q \in TranExclusive(w)  BY <7>qnw DEF Tran, TranExclusive
            <7>bound2. TranExclusive(w) \subseteq known_messages[self] \cup {mm \in Network : Sig(mm) = self}
              BY <6>sscase, SelfSentBoundedInvT DEF SelfSentBoundedInvT
            <7>qkorself. q \in known_messages[self] \/ q \in {mm \in Network : Sig(mm) = self}
              BY <7>qte, <7>bound2
            <7>qisprop. IsProposal(q)  OBVIOUS
            <7>notselfprop. q \notin {mm \in Network : Sig(mm) = self}
              <8> SUFFICES ASSUME q \in {mm \in Network : Sig(mm) = self} PROVE FALSE  OBVIOUS
              <8>1. q \in Network /\ Sig(q) = self  OBVIOUS
              <8> QED BY <8>1, <7>qisprop, SelfSentNotProposalInvT DEF SelfSentNotProposalInvT
            <7>qk. q \in known_messages[self]  BY <7>qkorself, <7>notselfprop
            <7>qbound. B(q) <= b  BY <7>qk, <7>qisprop, <3>bound2
            <7>qbw. B(q) = B(w)  OBVIOUS
            <7> QED BY <7>qbound, <7>qbw
          <6> QED BY <6>kpcase, <6>sscase
        <5>xachieve. \E q \in Tran(x) : IsProposal(q) /\ ProposalBal(q) = b /\ B(q) = b
          <6>ach. \E q \in Tran(x) : IsProposal(q) /\ ProposalBal(q) = B(x) /\ B(q) = B(x)
            BY BAchievedByProposal
          <6> QED BY <6>ach, <3>contribcase
        <5> PICK qx \in Tran(x) : IsProposal(qx) /\ ProposalBal(qx) = b /\ B(qx) = b  BY <5>xachieve
        <5>qxTU. qx \in TU
          <6>1. Tran(x) \subseteq (known_messages[self] \cup {x})
            <7>a. x \in (known_messages[self] \cup {x})  OBVIOUS
            <7>b. TranExclusive(x) \subseteq (known_messages[self] \cup {x})  BY <2>xte
            <7>c. Tran(x) = {x} \cup TranExclusive(x)  BY DEF Tran, TranExclusive
            <7> QED BY <7>a, <7>b, <7>c
          <6> QED BY <6>1
        <5>ybal. B(y0) = b
          <6> DEFINE Cand == Proposals \cap Tran(y0)
          <6>tranY. Tran(y0) = {y0} \cup TU  BY <5>KPT DEF Tran, TranExclusive
          <6>candeq. Cand = Proposals \cap TU
            <7>1. y0 \notin Proposals  BY <5>ynotprop
            <7> QED BY <6>tranY, <7>1
          <6>qxincand. qx \in Cand
            <7>a. qx \in Proposals  BY DEF IsProposal
            <7> QED BY <6>candeq, <7>a, <5>qxTU
          <6>ubound. \A z \in Cand : ProposalBal(z) <= b
            <7> SUFFICES ASSUME NEW z \in Cand PROVE ProposalBal(z) <= b  OBVIOUS
            <7>1. z \in TU  BY <6>candeq
            <7>2. IsProposal(z)  BY <6>candeq DEF IsProposal
            <7>3. z \in Messages  BY <7>1, <2>xte, <2>xmsg, <1>i
            <7>4. z \in GetProposals(z)
              <8>1. z \in Tran(z)  BY DEF Tran
              <8> QED BY <8>1, <6>candeq DEF GetProposals
            <7>5. ProposalBal(z) <= B(z)
              <8>fin. IsFiniteSet(GetProposals(z))
                <9>1. GetProposals(z) \subseteq Tran(z)  BY DEF GetProposals
                <9>2. IsFiniteSet(Tran(z))  BY <7>3, <5>mi DEF TranFinite
                <9> QED BY <9>1, <9>2, FS_Subset
              <8>sub. GetProposals(z) \subseteq Proposals  BY DEF GetProposals
              <8>ne. GetProposals(z) # {}  BY <7>4
              <8>choose. /\ B(z) \in {ProposalBal(w) : w \in GetProposals(z)}
                         /\ \A ww \in {ProposalBal(w) : w \in GetProposals(z)} : B(z) >= ww
                BY <8>fin, <8>sub, <8>ne, <5>mi, MaxBSetProperty DEF B
              <8>mem. ProposalBal(z) \in {ProposalBal(w) : w \in GetProposals(z)}  BY <7>4
              <8> QED BY <8>choose, <8>mem
            <7>6. B(z) <= b  BY <7>1, <5>tbound2
            <7>7. ProposalBal(z) \in Ballots
              <8>1. MessageInterface.proposalbal \in [Proposals -> Ballots]
                BY <5>mi DEF TypeOKMessageInterface
              <8>2. z \in Proposals  BY <7>2 DEF IsProposal
              <8> QED BY <8>1, <8>2 DEF ProposalBal
            <7>8. B(z) \in Ballots  BY <5>mi, <7>3, BBallot
            <7>9. b \in Ballots  OBVIOUS
            <7> QED BY <7>5, <7>6, <7>7, <7>8, <7>9, LeTransBallotsT
          <6>candfin. IsFiniteSet(Cand)
            <7>ysub. Cand \subseteq Tran(y0)  OBVIOUS
            <7>yfin. IsFiniteSet(Tran(y0))  BY <5>mi, <5>y0msg DEF TranFinite
            <7> QED BY <7>ysub, <7>yfin, FS_Subset
          <6>candsub. Cand \subseteq Proposals  OBVIOUS
          <6>candne. Cand # {}  BY <6>qxincand
          <6>ychoose. /\ B(y0) \in {ProposalBal(w) : w \in Cand}
                      /\ \A ww \in {ProposalBal(w) : w \in Cand} : B(y0) >= ww
            BY <6>candfin, <6>candsub, <6>candne, <5>mi, MaxBSetProperty DEF B, GetProposals
          <6>yge. B(y0) >= b
            <7>1. ProposalBal(qx) \in {ProposalBal(w) : w \in Cand}  BY <6>qxincand
            <7> QED BY <7>1, <6>ychoose
          <6>yle. B(y0) <= b
            <7>pw. PICK w \in Cand : B(y0) = ProposalBal(w)  BY <6>ychoose
            <7> QED BY <7>pw, <6>ubound
          <6>yty. y0 \in Messages  BY <5>y0propsU
          <6>ybalty. B(y0) \in Ballots  BY <5>mi, <6>yty, BBallot
          <6>bty. b \in Ballots  OBVIOUS
          <6> QED BY <6>yge, <6>yle, <6>ybalty, <6>bty, EqFromLeGeBallotsT
        <5>qdeq. {q \in TranExclusive(y0) : B(y0) = B(q) /\ HasDepth(alpha, q, d-1)}
                   = {xx \in TU : B(xx) = b /\ HasDepth(alpha, xx, d-1)}
          BY <5>KPT, <5>ybal
        <5>dpos. d >= 1  OBVIOUS
        <5>qdval. Qd(alpha, y0, d) = {xx \in TU : B(xx) = b /\ HasDepth(alpha, xx, d-1)}
          BY <5>dpos, <5>qdeq DEF Qd
        <5>subKPT. {xx \in (known_messages[self] \cup {x}) : B(xx) = b /\ HasDepth(alpha, xx, d-1)}
                     \subseteq {xx \in TU : B(xx) = b /\ HasDepth(alpha, xx, d-1)}
          OBVIOUS
        <5>sigsub. SigS({xx \in (known_messages[self] \cup {x}) : B(xx) = b /\ HasDepth(alpha, xx, d-1)})
                     \subseteq SigS(Qd(alpha, y0, d))
          BY <5>subKPT, <5>qdval DEF SigS
        <5>qdfin. IsFiniteSet(Qd(alpha, y0, d))
          <6>1. Qd(alpha, y0, d) \subseteq TU  BY <5>qdval
          <6>2. IsFiniteSet(TU)
            <7>0. known_messages[self] \subseteq Network  BY <1>i
            <7>0b. IsFiniteSet(known_messages[self])  BY <7>0, <1>i, FS_Subset
            <7>1. IsFiniteSet(known_messages[self] \cup {x})  BY <7>0b, FS_AddElement
            <7>2. IsFiniteSet({mm \in Network : Sig(mm) = self})  BY <1>i, FS_Subset
            <7> QED BY <7>1, <7>2, FS_Union
          <6> QED BY <6>1, <6>2, FS_Subset
        <5>sigfin. IsFiniteSet(SigS(Qd(alpha, y0, d)))  BY <5>qdfin, FS_Image DEF SigS
        <5>sigacc. SigS(Qd(alpha, y0, d)) \subseteq Acceptors
          <6> SUFFICES ASSUME NEW aa \in SigS(Qd(alpha, y0, d)) PROVE aa \in Acceptors  OBVIOUS
          <6>1. PICK q \in Qd(alpha, y0, d) : aa = Sig(q)  BY DEF SigS
          <6>2. HasDepth(alpha, q, d-1)  BY <6>1, <5>qdval
          <6>3. Sig(q) \in Acceptors  BY <6>2 DEF HasDepth
          <6> QED BY <6>1, <6>3
        <5>quo. SigS(Qd(alpha, y0, d)) \in Quorums(alpha)
          BY <5>sigsub, <5>sigfin, <5>sigacc, <4>quoKPpre, QuorumUpward
        <5>hd. HasDepth(alpha, y0, d)
          <6>ysig. Sig(y0) \in Acceptors  BY <2>1a, <5>y0sig, SafeAcceptorsSubsetAcceptors
          <6>hddef. HasDepth(alpha, y0, d) =
                      (/\ Sig(y0) \in Acceptors
                       /\ IF d = 0 THEN (IsOneB(y0) /\ Fresh(alpha, y0))
                                   ELSE SigS(Qd(alpha, y0, d)) \in Quorums(alpha))
            BY <5>mi, <5>y0msg, HasDepthDef
          <6>dne0. d # 0  BY <5>dpos
          <6> QED BY <6>ysig, <6>hddef, <6>dne0, <5>quo
        <5>hd1. HasDepth(alpha, y0, 1)
          <6>lga. LearnersMightAgree /\ ValidLearnerGraphAssumption  BY DEF LearnerGraphAssumptions
          <6> QED BY <5>mi, <5>y0msg, <6>lga, <5>hd, <5>dpos, HasDepthDownward
        <5>istwoa. IsTwoA(y0)
          <6>1. ~IsProposal(y0)  BY <5>ynotprop DEF IsProposal
          <6> QED BY <6>1, <5>hd1 DEF IsTwoA
        <5>y0any. B(y0) = b /\ HasDepth(alpha, y0, d) /\ IsTwoA(y0)
          BY <5>ybal, <5>hd, <5>istwoa
        <5> QED BY <5>y0in, <5>y0props, <5>y0any, <2>sceq
      <4> QED BY <4>case1, <4>case2
    <3>notcontribcase. CASE ~(B(x) = b /\ HasDepth(alpha, x, d-1))
      <4>seteq. {xx \in known_messages[self] : B(xx) = b /\ HasDepth(alpha, xx, d-1)}
                  = {xx \in (known_messages[self] \cup {x}) : B(xx) = b /\ HasDepth(alpha, xx, d-1)}
        BY <3>notcontribcase
      <4>quopre. SigS({xx \in known_messages[self] : B(xx) = b /\ HasDepth(alpha, xx, d-1)})
                   \in Quorums(alpha)
        <5>1. known_messages[self] \cup {x} = known_messages'[s]  BY <2>kself, <2>sceq
        <5>2. SigS({xx \in (known_messages[self] \cup {x}) :
                    B(xx) = b /\ HasDepth(alpha, xx, d-1)}) \in Quorums(alpha)
          BY <5>1
        <5> QED BY <4>seteq, <5>2
      <4>old. \E twoa \in Network : B(twoa) = b /\ Sig(twoa) = self /\ HasDepth(alpha, twoa, d) /\ IsTwoA(twoa)
        BY <3>bound2, <4>quopre, TwoAInvariantT DEF TwoAInvariantT
      <4> PICK twoa \in Network :
            B(twoa) = b /\ Sig(twoa) = self /\ HasDepth(alpha, twoa, d) /\ IsTwoA(twoa)  BY <4>old
      <4> QED BY <2>netmono, <2>sceq
    <3> QED BY <3>contribcase, <3>notcontribcase
  <2> QED BY <2>scase, <2>sceq
<1>4. CASE \E self \in ByzantineAcceptors : byz(self)
  <2>1. PICK self \in ByzantineAcceptors : byz(self)  BY <1>4
  <2>2. PICK y \in {z \in Messages : Sig(z) = self /\ TranExclusive(z) \subseteq Network} :
              Network' = (Network \cup {y})
     BY <2>1 DEF byz
  <2>k. known_messages' = known_messages  BY <2>1 DEF byz
  <2>netmono. Network \subseteq Network'  BY <2>2
  <2> SUFFICES ASSUME NEW s \in SafeAcceptors, NEW b \in Ballots, NEW alpha \in Learners,
                      NEW d \in (1..MaxDepth(alpha)),
                      \A xx \in known_messages'[s] : (IsProposal(xx) => B(xx) <= b),
                      SigS({xx \in known_messages'[s] :
                            B(xx) = b /\ HasDepth(alpha, xx, d-1)}) \in Quorums(alpha)
               PROVE \E twoa \in Network' :
                       B(twoa) = b /\ Sig(twoa) = s /\ HasDepth(alpha, twoa, d) /\ IsTwoA(twoa)
    BY DEF TwoAInvariantT
  <2>keq. known_messages'[s] = known_messages[s]  BY <2>k
  <2>bound. \A xx \in known_messages[s] : (IsProposal(xx) => B(xx) <= b)  BY <2>keq
  <2>quo. SigS({xx \in known_messages[s] : B(xx) = b /\ HasDepth(alpha, xx, d-1)}) \in Quorums(alpha)
    BY <2>keq
  <2>old. \E twoa \in Network : B(twoa) = b /\ Sig(twoa) = s /\ HasDepth(alpha, twoa, d) /\ IsTwoA(twoa)
    BY <2>bound, <2>quo, TwoAInvariantT DEF TwoAInvariantT
  <2> PICK twoa \in Network : B(twoa) = b /\ Sig(twoa) = s /\ HasDepth(alpha, twoa, d) /\ IsTwoA(twoa)
    BY <2>old
  <2> QED BY <2>netmono
<1> QED BY <1>2, <1>3, <1>4 DEF Next

LEMMA TwoAHoldsT ==
  (Spec /\ MessageInterfaceAssumptions /\ LearnerGraphAssumptions) => []TwoAInvariantT
<1> SUFFICES ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions
             PROVE Spec => []TwoAInvariantT  OBVIOUS
<1>1. Init => TwoAInvariantT  BY InitTwoAT
<1>2. AuxT /\ TwoAInvariantT /\ [Next]_vars => TwoAInvariantT'
  BY TwoAStepT, MessageInterfaceAssumptions, LearnerGraphAssumptions DEF AuxT
<1>3. Spec => []AuxT  BY AuxHoldsT
<1> QED BY <1>1, <1>2, <1>3, PTL DEF Spec, AuxT

LEMMA TwoAInvariantEqT == TwoAInvariantT => TwoAInvariant
BY DEF TwoAInvariantT, TwoAInvariant

LEMMA AlwaysTwoAInvariant ==
  (/\ Spec
   /\ MessageInterfaceAssumptions
   /\ ValueInterfaceAssumptions
   /\ LearnerGraphAssumptions
  )=> []TwoAInvariant
<1> SUFFICES ASSUME Spec, MessageInterfaceAssumptions, ValueInterfaceAssumptions, LearnerGraphAssumptions
             PROVE []TwoAInvariant  OBVIOUS
<1>1. []TwoAInvariantT  BY TwoAHoldsT
<1> QED BY <1>1, TwoAInvariantEqT, PTL
  

\* proving this probably will want to use DecideableProposalPExists 
THEOREM TemporalDecideableProposalExists ==
  (/\ Spec
   /\ MessageInterfaceAssumptions
   /\ ValueInterfaceAssumptions
   /\ LearnerGraphAssumptions
   /\ NetworkAssumption 
  ) =>
  \A alpha \in Learners :
  \A bal \in Ballots :
  \* M are all the messages with bal or lower
  LET M == {m \in Messages : ((B(m) <= bal) /\ (<>(m \in Network)))}
  IN \E p \in Proposals :
     (/\ TranExclusive(p) = DecideableProposalTranExclusive(M)
      /\ V(p) = DecideableProposalV(alpha, bal, M))
<1> SUFFICES ASSUME Spec, MessageInterfaceAssumptions, ValueInterfaceAssumptions,
                    LearnerGraphAssumptions, NetworkAssumption,
                    NEW alpha \in Learners, NEW bal \in Ballots
             PROVE LET M == {m \in Messages : ((B(m) <= bal) /\ (<>(m \in Network)))}
                   IN \E p \in Proposals :
                      (/\ TranExclusive(p) = DecideableProposalTranExclusive(M)
                       /\ V(p) = DecideableProposalV(alpha, bal, M))
  OBVIOUS
<1> DEFINE M == {m \in Messages : ((B(m) <= bal) /\ (<>(m \in Network)))}
<1>Msub. M \subseteq Messages  OBVIOUS
<1>mi. TypeOKMessageInterface /\ TranTrans /\ TranFinite /\ AlwaysAProposal
  BY DEF MessageInterfaceAssumptions
<1>balnat. bal \in Nat  BY DEF Ballots
<1>bp1nat. bal+1 \in Nat  BY <1>balnat
<1>bp1bal. bal+1 \in Ballots  BY <1>bp1nat DEF Ballots
<1>bound. \A y \in TranClosure(M) : B(y) < bal+1
  <2> SUFFICES ASSUME NEW y \in TranClosure(M) PROVE B(y) < bal+1  OBVIOUS
  <2>1. PICK m \in M : y \in Tran(m)  BY DEF TranClosure
  <2>2. m \in Messages /\ B(m) <= bal  BY <2>1
  <2>3. B(y) <= B(m)  BY <2>1, <2>2, <1>mi, BMonotone
  <2>ym. y \in Messages  BY <2>1, <2>2, <1>mi, TranSubMessages
  <2>ybal. B(y) \in Ballots  BY <2>ym, <1>mi, BBallot
  <2>mbal. B(m) \in Ballots  BY <2>2, <1>mi, BBallot
  <2>4. B(y) <= bal  BY <2>3, <2>2, <2>ybal, <2>mbal, <1>balnat, LeTransBallotsT
  <2> QED BY <2>4, <1>balnat, <2>ybal DEF Ballots
<1>via. AlwaysAValue  BY DEF ValueInterfaceAssumptions
<1> DEFINE S == ConFromCaught(alpha, CaughtS(TranClosure(M)))
<1> DEFINE SS == S \cap RelevantLearners(M)
<1>tval. DecideableProposalV(alpha, bal, M) \in Values
  <2>caseE. CASE SS = {}
    <3>1. DecideableProposalV(alpha,bal,M) = BalToVal(bal)  BY <2>caseE DEF DecideableProposalV
    <3> QED BY <3>1, <1>via, <1>balnat DEF AlwaysAValue
  <2>caseNE. CASE SS # {}
    <3>ssL. SS \in SUBSET Learners
      <4>1. RelevantLearners(M) \subseteq Learners  BY DEF RelevantLearners
      <4> QED BY <4>1
    <3>ssrel. \A beta \in SS : \E x \in TranClosure(M) : beta \in Lrns(x)
      <4> SUFFICES ASSUME NEW beta \in SS PROVE \E x \in TranClosure(M) : beta \in Lrns(x)  OBVIOUS
      <4>1. beta \in RelevantLearners(M)  OBVIOUS
      <4> QED BY <4>1 DEF RelevantLearners
    <3>bse. \E beta \in SS : \A gamma \in SS : BXBeta(M,gamma) <= BXBeta(M,beta)
      BY <3>ssL, <2>caseNE, <3>ssrel, <1>bp1nat, <1>bound, BetaStarExists
    <3> DEFINE betastar == CHOOSE beta \in SS : \A gamma \in SS : BXBeta(M,gamma) <= BXBeta(M,beta)
    <3>bsprop. betastar \in SS /\ (\A gamma \in SS : BXBeta(M,gamma) <= BXBeta(M,betastar))
      BY <3>bse
    <3>bsRel. betastar \in RelevantLearners(M)  BY <3>bsprop
    <3>xbmsgs. TopLearnerMsg(M,betastar) \in TranClosure(M)
      <4>ex. \E x \in TranClosure(M) : betastar \in Lrns(x)  BY <3>bsRel DEF RelevantLearners
      <4> QED BY <4>ex, <1>mi, <1>bp1nat, <1>bound, TopLearnerMsgCorrect
    <3>xbm. TopLearnerMsg(M,betastar) \in Messages  BY <3>xbmsgs, <1>mi, TranClosureClosed
    <3>vval. V(TopLearnerMsg(M,betastar)) \in Values
      <4>1. B(TopLearnerMsg(M,betastar)) \in Ballots  BY <3>xbm, <1>mi, BBallot
      <4> QED BY <4>1, <1>via DEF V, AlwaysAValue
    <3>dpv. DecideableProposalV(alpha,bal,M) = V(TopLearnerMsg(M,betastar))
      BY <2>caseNE DEF DecideableProposalV
    <3> QED BY <3>dpv, <3>vval
  <2> QED BY <2>caseE, <2>caseNE
<1>pex. \E p \in Proposals :
          /\ TranExclusive(p) = TranClosure(CQ(M))
          /\ B(p) > bal+1
          /\ Sig(p) \notin Acceptors
          /\ V(p) = DecideableProposalV(alpha, bal, M)
  BY <1>Msub, <1>bp1bal, <1>tval, <1>bound, MessageInterfaceAssumptions, LearnerGraphAssumptions,
     ValueInterfaceAssumptions, PExists
<1> PICK p \in Proposals :
      /\ TranExclusive(p) = TranClosure(CQ(M))
      /\ B(p) > bal+1
      /\ Sig(p) \notin Acceptors
      /\ V(p) = DecideableProposalV(alpha, bal, M)
  BY <1>pex
<1> QED BY DEF DecideableProposalTranExclusive

\* proving this will probably want to use DecideableProposalOneBExists, AlwaysOneBInvariant, AlwaysTwoAInvariant, and EventuallyKnown
THEOREM TerminatingProposal ==
  (/\ Spec
   /\ MessageInterfaceAssumptions
   /\ ValueInterfaceAssumptions
   /\ LearnerGraphAssumptions
   /\ NetworkAssumption 
  ) =>
  \A alpha \in Learners :
  \A bal \in Ballots :
  \A p \in Proposals :
  \* M are all the messages with bal or lower
  LET M == {m \in Messages : ((B(m) <= bal) /\ (<>(m \in Network)))}
  IN TranExclusive(p) = DecideableProposalTranExclusive(M) =>
     V(p) = DecideableProposalV(alpha, bal, M) =>
      \* alpha has a live quorum
     LiveAcceptors \in Quorums(alpha) =>
        \* p is the only proposal not in M that will ever be sent
     (\A x \in Proposals : (((<>(x \in Network)) /\ (B(x) > bal)) => (x = p))) =>
       \* and p is eventually sent
     (<>(p \in Network)) =>
       \* alpha eventually decides
     (<>(Decision(Network, alpha, B(p))))


\* proving this will probably want to use TerminatingProposal  and TemporalDecideableProposalExists
\*
\*
\* In principle, this could be re-worked into the spec so that
\*  byz can propose anything up to bal, and only some specific
\*  proposer can propose (and only once) the correct proposal above bal.
\* This requires the proposer be able to see the future, 
\*  since the proposal is calculated using <> statements.
\* We could instead explicitly model a more complicated network 
\*  that the proposer is allowed to monitor / control at some point.
\* For now, I'm just going to do it this way.
THEOREM Termination ==
  (/\ Spec
   /\ MessageInterfaceAssumptions
   /\ ValueInterfaceAssumptions
   /\ LearnerGraphAssumptions
   /\ NetworkAssumption 
  ) =>
  \A alpha \in Learners :
  \A bal \in Ballots :
   \* alpha has a live quorum
  LiveAcceptors \in Quorums(alpha) =>
    \* alpha must agree with itself; not sure if we must state this explicitly
    \*   SafeAcceptors \in SafetySets({alpha}) =>
    \* there is some "correct" proposal p such that
  \E p \in Proposals : \* TerminatingProposal "defines" this in terms of value and Tran
     \* if no proposal that will ever be sent except p has a ballot > bal
  (\A x \in Proposals : (((<>(x \in Network)) /\ (B(x) > bal)) => (x = p))) =>
    \* and p is eventually sent
  (<>(p \in Network)) =>
    \* alpha eventually decides
  (<>(Decision(Network, alpha, B(p))))




============================================================================
