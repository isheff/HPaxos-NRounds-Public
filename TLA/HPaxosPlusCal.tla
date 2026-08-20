-------------------------- MODULE HPaxosPlusCal --------------------------
\* A PlusCal model of the message network for the honest (safe) acceptors.
\*
\*   - Msgs      : the set of messages that have ever been sent.  Grows only.
\*   - known_messages[s] : the messages safe acceptor s has learned.  Grows only.
\*
\* Each safe acceptor s is modeled as one process PER (s, x) PAIR it might ever
\* receive.  That process's single step does two things atomically:
\*   1. Learn message x from the Msgs.  This is only allowed if s already
\*      knows every message in TranExclusive(x) (its whole prior history).
\*   2. Forced send: if -- once x is learned -- there exists a message y signed
\*      by s whose exclusive transitive history TranExclusive(y) is EXACTLY the
\*      set (known_messages[s] with x added) \cup (messages already signed by s
\*      in the Msgs), then s MUST send y (add it to the Msgs).
\*
\* The forced-send set is exactly one message shape (its history is pinned down
\* to a specific set), so at most one y qualifies up to that history.
\*
\* Byzantine senders (Senders \ SafeAcceptors) ignore known_messages entirely:
\* at any time such an s may send ANY message it signs whose exclusive history
\* is already fully in the Msgs.  This is any non-safe sender, not just
\* non-safe acceptors -- e.g. it also covers proposers behaving adversarially.
\* MessageInterface is the only import needed, and it must be EXTENDS: the
\* definitions below (Inv, CP_Hyp, the *InvT invariants, ...) have bodies
\* mentioning its operators, and every consumer that unfolds one of them must
\* see the SAME copy. LOCAL INSTANCE would hand this module private copies and
\* consumer proofs would fail on renamed-apart operators.
\*
\* Dropped from the unsplit NetworkSpec header, all redundant or unused here:
\*   Naturals              -- re-exported already, via MessageInterface ->
\*                            ValueInterface -> Naturals (and Integers via
\*                            LearnerGraphInterface -> FiniteSetsExt)
\*   TLAPS                 -- supplies PTL / backend method operators and the
\*                            standard theorems, all proof-only; this module
\*                            has no proofs. The temporal operators used below
\*                            ([], <>, ~>, WF_) are core TLA+, not TLAPS.
\*   FiniteSetTheorems     -- its FS_* theorems are proof-only and uncited
\*                            here, and IsFiniteSet already arrives through
\*                            MessageInterface. Keeping it as LOCAL INSTANCE
\*                            would put a SECOND copy of IsFiniteSet in scope
\*                            (the IsFiniteSet_1 clash), breaking the first
\*                            lemma module that unfolds Inv or CP_Hyp.
EXTENDS MessageInterface

CONSTANT SafeAcceptors
SafeAcceptorsAssumption == SafeAcceptors \subseteq Acceptors

\* Live acceptors are safe acceptors whose step is required (weakly fairly) to
\* eventually happen when continuously enabled -- see NetworkAssumption below.
CONSTANT LiveAcceptors
LiveAcceptorsAssumption == LiveAcceptors \subseteq SafeAcceptors

AcceptorsAssumptions == (SafeAcceptorsAssumption /\ LiveAcceptorsAssumption)

ByzSenders == Senders \ SafeAcceptors

(* --algorithm HPaxosPlusCal {
     variables
       Msgs = {},
       known_messages = [s \in SafeAcceptors |-> {}];

     \* One process per (safe acceptor, message) PAIR: whenever that message's
     \* whole prior history is already known to that acceptor, learn it (and
     \* forced-send).  Indexing by the pair -- rather than one process per
     \* acceptor with an internal `with` over the message -- means weak fairness
     \* can be imposed directly on each (acceptor, message) process (see
     \* NetworkAssumption), with no separate operator needed to relate the
     \* fairness action to the system's step relation.
     \* self[1] is the acceptor; self[2] is the message.
     process (safe_acceptor_receives_message \in SafeAcceptors \times Messages)
     {
       lstep:
         while (TRUE) {
           when self[2] \in Msgs;
           when TranExclusive(self[2]) \subseteq known_messages[self[1]];
           known_messages[self[1]] := known_messages[self[1]] \cup {self[2]};
           \* Forced send: if a message signed by self[1] with history exactly
           \* (known_messages[self[1]] with self[2], plus self[1]'s own
           \* sent messages) exists, one such message MUST be sent -- ANY
           \* such witness (the choice is nondeterministic: witnesses agree
           \* on their history but may differ in their priors field, which
           \* the interface does not observe).
           either {
             with (y \in LET T == (known_messages[self[1]] \cup {self[2]})
                                  \cup {m \in Msgs : Sig(m) = self[1]}
                         IN {z \in (Messages \ Proposals) :
                               Sig(z) = self[1] /\ TranExclusive(z) = T}) {
               Msgs := Msgs \cup {y};
             }
           } or {
             when LET T == (known_messages[self[1]] \cup {self[2]})
                           \cup {m \in Msgs : Sig(m) = self[1]}
                  IN ~\E z \in (Messages \ Proposals) :
                        Sig(z) = self[1] /\ TranExclusive(z) = T;
             skip;
           };
         }
     }

     process (byz \in ByzSenders)
     {
       bstep:
         while (TRUE) {
           \* Those who aren't safeacceptors (byzantine, or proposers)
           \*  are modeled as able to send anything they can sign, so
           \*  long as TranExclusive() is already sent.
           with (y \in {z \in Messages : Sig(z) = self /\ TranExclusive(z) \subseteq Msgs}) {
             Msgs := Msgs \cup {y};
           }
         }
     }
   }
*)
\* BEGIN TRANSLATION (chksum(pcal) = "986ee6e0" /\ chksum(tla) = "e530e0fb")
VARIABLES Msgs, known_messages

vars == << Msgs, known_messages >>

ProcSet == (SafeAcceptors \times Messages) \cup (ByzSenders)

Init == (* Global variables *)
        /\ Msgs = {}
        /\ known_messages = [s \in SafeAcceptors |-> {}]

safe_acceptor_receives_message(self) == /\ self[2] \in Msgs
                                        /\ TranExclusive(self[2]) \subseteq known_messages[self[1]]
                                        /\ known_messages' = [known_messages EXCEPT ![self[1]] = known_messages[self[1]] \cup {self[2]}]
                                        /\ \/ /\ \E y \in LET T == (known_messages'[self[1]] \cup {self[2]})
                                                                   \cup {m \in Msgs : Sig(m) = self[1]}
                                                          IN {z \in (Messages \ Proposals) :
                                                                Sig(z) = self[1] /\ TranExclusive(z) = T}:
                                                   Msgs' = (Msgs \cup {y})
                                           \/ /\ LET T == (known_messages'[self[1]] \cup {self[2]})
                                                          \cup {m \in Msgs : Sig(m) = self[1]}
                                                 IN ~\E z \in (Messages \ Proposals) :
                                                       Sig(z) = self[1] /\ TranExclusive(z) = T
                                              /\ TRUE
                                              /\ Msgs' = Msgs

byz(self) == /\ \E y \in {z \in Messages : Sig(z) = self /\ TranExclusive(z) \subseteq Msgs}:
                  Msgs' = (Msgs \cup {y})
             /\ UNCHANGED known_messages

Next == (\E self \in SafeAcceptors \times Messages: safe_acceptor_receives_message(self))
           \/ (\E self \in ByzSenders: byz(self))

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
\*
\* WEAKENED (branch weakened-network-assumption): fairness is owed only for
\* messages that are LIVE-RELEVANT -- sent by (Sig) or known to
\* (known_messages) some live acceptor.  Formally, WF is imposed on the
\* receive action RESTRICTED by the LiveRelevant state predicate: if the
\* restricted action is continuously enabled (message deliverable AND
\* currently live-relevant), it must eventually be taken.  For a message that
\* never becomes live-relevant the restricted action is never enabled and the
\* obligation is vacuous.  LiveRelevant is monotone under Spec (known_messages
\* only grows, Sig is constant), so this is equivalent under Spec to the
\* conditional form  <>LiveRelevant(self[2]) => WF_vars(receive(self)).
LiveRelevant(x) ==
  \/ Sig(x) \in LiveAcceptors
  \/ \E b \in LiveAcceptors : x \in known_messages[b]

\* The receive action restricted to live-relevant messages.  Kept as a named
\* top-level operator so WF_vars/ENABLED facts about it stay opaque
\* applications: congruence through WF_vars does not fire on
\* syntactically-built tuples, so call sites get their literal-tuple instances
\* via lemma application (NetworkAssumptionInst) against this symbol.
relevant_receive(self) ==
  safe_acceptor_receives_message(self) /\ LiveRelevant(self[2])

NetworkAssumption ==
  \A self \in LiveAcceptors \times Messages : WF_vars(relevant_receive(self))

\* Unconditional per-message fairness restricted to the transitive history
\* Tran(pp) of a single message pp.  NOT part of NetworkAssumption: the
\* termination theorems take TranFairness(p) for their designated proposal p
\* as an extra hypothesis.  Under the weakened NetworkAssumption alone,
\* LiveRelevant never bootstraps for a Byzantine-signed proposal (its first
\* receipt is never forced: nobody live signed it and nobody live knows it),
\* so p's delivery -- and that of its exclusive history, which gates the
\* enabledness of receiving p -- must be assumed fair separately.  Tran is
\* transitively closed (TranTrans), which is exactly what the restricted
\* KnowLeadsToTran induction needs.
TranFairness(pp) ==
  \A self \in LiveAcceptors \times Tran(pp) :
    WF_vars(safe_acceptor_receives_message(self))


\* ==========================================================================
\* Defined for use in lemmas
\* ==========================================================================
\* Everything below appears part-way through the unsplit NetworkSpec,
\* interleaved with the lemmas and theorems that consume it.  Collected here
\* so each lemma can live in its own module: a lemma module that unfolds one
\* of these needs only to EXTENDS HPaxosPlusCal, rather than EXTENDS whatever
\* module happened to hold the definition.
\*
\* Many are deliberately-shaped wrappers rather than conveniences -- the
\* *op-suffixed operators exist to make temporal conclusions opaque so they
\* can be instantiated at concrete arguments, and several bound-variable
\* names are pinned to match their producers because TLAPS will not
\* alpha-rename inside a []. Those comments are preserved verbatim.

\* The live-relevant portion of the sent set.  Monotone under Spec (Msgs and
\* known_messages only grow; Sig is constant), and closed under TranExclusive
\* at reachable states (BoxRelTranClosed, from AuxT): a live-signed message's
\* history is bounded by its signer's knowledge (SelfSentBoundedInvT), and a
\* known message's history is known (KnownTranClosureInvT).
RelevantMsgs == {x \in Msgs : LiveRelevant(x)}

\* WEAKENED with NetworkAssumption: only live-relevant messages are promised
\* to become known to every live acceptor.  (The unweakened form -- source
\* m \subseteq Msgs -- is FALSE under the weakened NetworkAssumption: a
\* Byzantine-signed message nobody live ever receives is a countermodel.)
EventuallyKnownInvariant ==
  \A m \in SUBSET Messages :
    (m \subseteq RelevantMsgs) ~>
    (\A a \in LiveAcceptors : m \subseteq known_messages[a])

SafeAcceptorsUncaughtInvariant ==
  SafeAcceptors \cap CaughtS(Msgs) = {}

DecisionStableInvariant ==
  \A alpha \in Learners :
  \A bal \in Ballots :
  Decision(Msgs, alpha, bal) => []Decision(Msgs, alpha, bal)

AgreementInvariant ==
  \A alpha \in Learners :
  \A beta  \in Learners :
  \A alphabal \in Ballots :
  \A betabal  \in Ballots :
  (/\ SafeAcceptors \in SafetySets({alpha, beta})
   /\ Decision(Msgs, alpha, alphabal)
   /\ Decision(Msgs, beta,  betabal )
  ) => BalToVal(alphabal) = BalToVal(betabal)

OneBInvariant ==
  \A s \in SafeAcceptors :
  \A b \in Ballots :
  \A p \in known_messages[s] :
  (/\ B(p) = b
   /\ IsProposal(p)
   /\ \A x \in known_messages[s] : IsProposal(x) => B(x) <= b
  ) => \E oneb \in Msgs :
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
  ) => \E twoa \in Msgs :
  (/\ B(twoa) = b
   /\ Sig(twoa) = s
   /\ HasDepth(alpha, twoa, d)
   /\ IsTwoA(twoa))


\* ===================================================================
\* Inductive invariant
\* ===================================================================
Inv ==
  /\ Msgs \in SUBSET Messages
  /\ known_messages \in [SafeAcceptors -> SUBSET Messages]
  /\ IsFiniteSet(Msgs)
  /\ \A s \in SafeAcceptors : known_messages[s] \subseteq Msgs
  /\ \A z \in Msgs : TranExclusive(z) \subseteq Msgs

\* Operator-laundering wrapper: SANY's higher-order level check does not
\* recurse into instantiated bodies, so BoxAct(F) == []F lets a [](action)
\* premise be written without tripping a level error.
BoxAct(F) == []F

\* Single-message learn leads-to (WF1, boxed-premise recipe).  Sources are
\* subsets of RelevantMsgs (weakened NetworkAssumption reaches no further).
CP_Tgt(U)       == \A p \in U : p[2] \in known_messages[p[1]]
CP_LT(Src, p)   == (Spec /\ NetworkAssumption)
                     => ((Src \subseteq RelevantMsgs) ~> (p[2] \in known_messages[p[1]]))
CP_Good(Src, U) == /\ ((Spec /\ NetworkAssumption) => ((Src \subseteq RelevantMsgs) ~> CP_Tgt(U)))
                   /\ (Spec => [](CP_Tgt(U) => []CP_Tgt(U)))
CP_Hyp(Src, U)  == /\ IsFiniteSet(U) /\ U \subseteq SafeAcceptors \X Messages
                   /\ \A p \in U : CP_LT(Src, p)
CPLop(Src, SS)  == (Spec /\ NetworkAssumption) => ((Src \subseteq RelevantMsgs) ~> CP_Tgt(SS))

\* Clean-context helpers for the fragile INV1-style boxing (PTL chokes on the
\* heavy context inside ConjPairLeadsTo's induction).
KLT(a, xx)  == (Spec /\ NetworkAssumption) => ((xx \in RelevantMsgs) ~> (xx \in known_messages[a]))
SKSop(a, S) == Spec => [](S \subseteq known_messages[a] => [](S \subseteq known_messages[a]))
LLTop(a, xx) == (Spec /\ NetworkAssumption)
                  => ((xx \in RelevantMsgs /\ TranExclusive(xx) \subseteq known_messages[a])
                       ~> (xx \in known_messages[a]))

\* --- Tran(pp)-restricted leads-to plumbing (unconditional TranFairness) ---
\* Parallel family to CP_* / KLT / LLTop: same targets, but the fairness
\* hypothesis is TranFairness(pp) and the sources are plain Msgs-memberships,
\* exactly as in the unweakened development -- valid here because every pair's
\* message lies in Tran(pp), where WF is assumed outright.
CPT_LT(pp, Src, q)   == (Spec /\ TranFairness(pp))
                          => ((Src \subseteq Msgs) ~> (q[2] \in known_messages[q[1]]))
CPT_Good(pp, Src, U) == /\ ((Spec /\ TranFairness(pp)) => ((Src \subseteq Msgs) ~> CP_Tgt(U)))
                        /\ (Spec => [](CP_Tgt(U) => []CP_Tgt(U)))
CPT_Hyp(pp, Src, U)  == /\ IsFiniteSet(U) /\ U \subseteq SafeAcceptors \X Messages
                        /\ \A q \in U : CPT_LT(pp, Src, q)
CPTLop(pp, Src, SS)  == (Spec /\ TranFairness(pp)) => ((Src \subseteq Msgs) ~> CP_Tgt(SS))
KLTT(pp, a, xx)  == (Spec /\ TranFairness(pp)) => ((xx \in Msgs) ~> (xx \in known_messages[a]))
LLTTop(pp, a, xx) == (Spec /\ TranFairness(pp))
                       => ((xx \in Msgs /\ TranExclusive(xx) \subseteq known_messages[a])
                            ~> (xx \in known_messages[a]))
BTCop(xx, w) == Spec => [](({xx} \subseteq Msgs) => w \in Msgs)
BTPop(a, T)  == Spec => [](CP_Tgt({a} \X T) <=> (T \subseteq known_messages[a]))
NBop(xx)     == Spec => [](({xx} \subseteq Msgs) <=> (xx \in Msgs))
BKEop(p, a)  == Spec => [](p[2] \in known_messages[p[1]] <=> p[2] \in known_messages[a])

\* Product-set equivalence (explicit tuple reasoning; SMT/auto fail on it).
ELtgt(m)     == \A a \in LiveAcceptors : m \subseteq known_messages[a]
BTLop(m)     == Spec => [](CP_Tgt(LiveAcceptors \X m) <=> ELtgt(m))

\* RelevantMsgs analogues of the Msgs-source bridges above (same shapes, same
\* consumers, RelevantMsgs source).  BTCRop is the load-bearing one: it is the
\* TranExclusive-closedness of RelevantMsgs at reachable states.
NBRop(xx)       == Spec => [](({xx} \subseteq RelevantMsgs) <=> (xx \in RelevantMsgs))
BTCRop(xx, w)   == Spec => [](({xx} \subseteq RelevantMsgs) => w \in RelevantMsgs)
BMNRop(m, x)    == Spec => [](m \subseteq RelevantMsgs => x \in RelevantMsgs)
RelStableOp(xx) == Spec => [](xx \in RelevantMsgs => [](xx \in RelevantMsgs))
RelSubNetOp(m)  == Spec => [](m \subseteq RelevantMsgs => m \subseteq Msgs)

SafeAcceptorChainInv ==
  \A s \in SafeAcceptors : \A m1, m2 \in Msgs :
    (Sig(m1) = s /\ Sig(m2) = s) => (m1 \in Tran(m2) \/ m2 \in Tran(m1))

KnownTranClosureInvT ==
  \A s \in SafeAcceptors : TranClosure(known_messages[s]) = known_messages[s]

SelfSentBoundedInvT ==
  \A s \in SafeAcceptors : \A z \in Msgs :
    Sig(z) = s => TranExclusive(z) \subseteq known_messages[s] \cup {m \in Msgs : Sig(m) = s}

SelfSentNotProposalInvT ==
  \A s \in SafeAcceptors : \A z \in Msgs : Sig(z) = s => ~IsProposal(z)

OneBInvariantT ==
  \A s \in SafeAcceptors :
  \A b \in Ballots :
  \A p \in known_messages[s] :
  (/\ B(p) = b
   /\ IsProposal(p)
   /\ \A xx \in known_messages[s] : IsProposal(xx) => B(xx) <= b
  ) => \E oneb \in Msgs :
  (/\ B(oneb) = b
   /\ Sig(oneb) = s
   /\ IsOneB(oneb)
  )

AuxT == Inv /\ KnownTranClosureInvT /\ SelfSentBoundedInvT /\ SelfSentNotProposalInvT /\
        SafeAcceptorChainInv

TwoAInvariantT ==
  \A s \in SafeAcceptors :
  \A b \in Ballots :
  \A alpha \in Learners :
  \A d \in (1..(MaxDepth(alpha))) :
  (/\ (\A xx \in known_messages[s] : (IsProposal(xx) => B(xx) <= b))
   /\ SigS({xx \in known_messages[s] :
           B(xx) = b /\ HasDepth(alpha, xx, d-1)}) \in Quorums(alpha)
  ) => \E twoa \in Msgs :
  (/\ B(twoa) = b
   /\ Sig(twoa) = s
   /\ HasDepth(alpha, twoa, d)
   /\ IsTwoA(twoa))

IAMESCond(mm) == mm \in Messages /\ <>(mm \in Msgs)
IsAllMessagesEverSent(x) == \A mm : (mm \in x <=> IAMESCond(mm))

LowNowT(bal, m) ==
  \A w \in Messages : ((w \in Msgs) /\ (B(w) <= bal)) => w \in m

DZInvT(alpha, p, a) ==
  p \in known_messages[a] =>
    (\E y \in Msgs : Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,0))

\* Joint invariant bundling DZInvT with the five auxiliary invariants it needs
\* under the step.  A single-conjunction INV1 over this avoids the strengthened-
\* INV1-plus-HIDE assembly (whose HIDE <expr> lists SANY rejects): Init/step for
\* each conjunct are named, proven pieces, and the QED projects DZInvT back out.
DZJoint(alpha, p, a) ==
  /\ DZInvT(alpha, p, a)
  /\ Inv
  /\ KnownTranClosureInvT
  /\ SelfSentBoundedInvT
  /\ SelfSentNotProposalInvT
  /\ SafeAcceptorChainInv

FD_Tgt(U)    == U \subseteq Msgs
DiaMem(m)    == <>(m \in Msgs)
FD_Hyp(U)    == IsFiniteSet(U) /\ (\A m \in U : DiaMem(m))
FD_Good(U)   == <>(FD_Tgt(U))
ElStabOp(m)  == Spec => [](m \in Msgs => [](m \in Msgs))
SubStabOp(S) == Spec => [](S \subseteq Msgs => [](S \subseteq Msgs))

EKLT(mm)    == (mm \subseteq RelevantMsgs) ~> (\A a \in LiveAcceptors : mm \subseteq known_messages[a])
\* Wrapper for extracting EventuallyKnownInvariant's leads-to at a specific mm:
\* EventuallyKnownInvariant's \A ranges over a temporal (~>) body, so it is
\* instantiated via the []-Barcan-equality + opaque wrapper route.  Bound
\* variable mm matches EventuallyKnownInvariant's own (no []-alpha-rename).
EKBoxOp(mm) == [](EKLT(mm))

LiveAcceptorsSentDepthBallot(m, alpha, b, d) ==
  LiveAcceptors \subseteq SigS({x \in m : B(x) = b /\ HasDepth(alpha, x, d)})

\* Operator-wrapped boxed memberships, so the temporal-conclusion lemmas apply
\* at ANY concrete message (non-identity temporal-conclusion application fails
\* unless the conclusion is an opaque operator application).
NetMsgBoxOp(mm)     == [](mm \in Msgs => mm \in Messages)
AllMsgBoxOp(mm, am) == [](mm \in Msgs => mm \in am)

KnownNetBoxOp(s) == [](\A xx : xx \in known_messages[s] => xx \in Msgs)

KnownAllBoxOp(s, am) == [](\A xx : xx \in known_messages[s] => xx \in am)

WPrimeStep(am, alpha, p, d) ==
  { CHOOSE x \in am : (Sig(x) = aa /\ B(x) = B(p) /\ HasDepth(alpha, x, d)) : aa \in LiveAcceptors }

\* Per-acceptor "witness set sent leads to depth-(d+1) sent", TAKEN as a
\* hypothesis (a separate lemma produces it from TwoAInvariantT + EventuallyKnown).
\* Operator-wrapped so it can be instantiated at a concrete s.
TwoAStepLtOp(am, alpha, p, d, s) ==
  (Spec /\ NetworkAssumption) =>
    ((WPrimeStep(am, alpha, p, d) \subseteq Msgs)
     ~> (\E twoa \in Msgs : Sig(twoa) = s /\ B(twoa) = B(p) /\ HasDepth(alpha, twoa, d+1)))

\* Wrapped conclusion so it can be cited at WP := WPrimeStep(...) first-order.
TwoASafeConcl(am, alpha, p, d, s, WP) ==
  Spec => (IsAllMessagesEverSent(am)
           => [](WP \subseteq known_messages[s]
                 => (\E twoa \in Msgs :
                       Sig(twoa) = s /\ B(twoa) = B(p) /\ HasDepth(alpha, twoa, d+1))))

LASDBDecOp(alpha, allmessages, b) ==
  Spec => (IsAllMessagesEverSent(allmessages) => <>Decision(Msgs, alpha, b))

HighNowT(p, bal) ==
  \A z \in Proposals : ((z \in Msgs) /\ (B(z) > bal)) =>
    ((V(z) = V(p)) /\ ((B(z) < B(p)) \/ (z = p)))

\* Relaxed analogue of SelfKnownBoundedByUniqueT: everything self knows or has
\* sent is either low (<= bal) or a V(p)-valued message strictly below B(p).
AmNowT(am) == \A xx : (xx \in Msgs) => (xx \in am)

SelfKnownHypR(self, p, bal) ==
  /\ B(p) > bal
  /\ p \notin known_messages[self]
  /\ (\A z \in Proposals : ((z \in Msgs) /\ (B(z) > bal)) =>
       ((V(z) = V(p)) /\ ((B(z) < B(p)) \/ (z = p))))

OneBCBHypR(self, p, bal) ==
  /\ TranExclusive(p) \subseteq known_messages[self]
  /\ p \notin known_messages[self]
  /\ (\A ww \in known_messages[self] : IsProposal(ww) => B(ww) # B(p))
  /\ (\A ww \in known_messages[self] : IsProposal(ww) => B(ww) <= B(p))
  /\ self \notin CaughtS(TranClosure((known_messages[self] \cup {p})
                                      \cup {mm \in Msgs : Sig(mm) = self}))
  /\ B(p) > bal
  /\ (\A z \in Proposals : ((z \in Msgs) /\ (B(z) > bal)) =>
       ((V(z) = V(p)) /\ ((B(z) < B(p)) \/ (z = p))))

DPFreshHypR(alpha, bal, m, p, a, known, oneb, CS2) ==
  /\ alpha \in ConFromCaught(alpha, CaughtS(TranClosure(m)))
  /\ (\A x \in TranClosure(m) : B(x) <= bal)
  /\ DecideableProposalTranExclusive(m) \subseteq Tran(p)
  /\ B(p) > bal
  /\ Sig(p) \notin Acceptors
  /\ V(p) = DecideableProposalV(alpha, bal, m)
  /\ (\A w \in TranClosure(known \cup {p}) :
       (w # p) => (\/ ((B(w) <= bal) /\ (w \in TranClosure(m)))
                   \/ ((B(w) > bal) /\ (B(w) < B(p)) /\ (V(w) = V(p)))))
  /\ CaughtS(TranClosure(known \cup {p})) \subseteq CS2
  /\ (ConFromCaught(alpha, CS2) = ConFromCaught(alpha, CaughtS(TranClosure(m))))
  /\ Sig(oneb) = a
  /\ TranExclusive(oneb) = TranClosure(known \cup {p})
  /\ a \notin CaughtS(TranClosure(known \cup {p}))

DZLTHypR(alpha, bal, m, p, am) ==
  /\ alpha \in ConFromCaught(alpha, CaughtS(TranClosure(m)))
  /\ (\A x \in TranClosure(m) : B(x) <= bal)
  /\ DecideableProposalTranExclusive(m) \subseteq Tran(p)
  /\ B(p) > bal
  /\ Sig(p) \notin Acceptors
  /\ V(p) = DecideableProposalV(alpha, bal, m)
  /\ (ConFromCaught(alpha, CaughtS({ww \in am : B(ww) < B(p)}))
      = ConFromCaught(alpha, CaughtS(TranClosure(m))))
  /\ []HighNowT(p, bal)
  /\ []LowNowT(bal, m)
  /\ []AmNowT(am)
====================================================================
