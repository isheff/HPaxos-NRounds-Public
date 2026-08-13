-------------------------- MODULE HPaxosPlusCalConcrete --------------------------
\* The CONCRETE counterpart of HPaxosPlusCal: the same message network, but
\* written under the identification MessageInterface = CMI, so that a message
\* is literally a [sender, payload, priors] record and a safe acceptor SENDS by
\* BUILDING one rather than by CHOOSEing an abstract message with a prescribed
\* history.
\*
\*   - Msgs                : messages that have ever been sent.  Grows only.
\*   - known_messages[s]   : messages safe acceptor s has learned.  Grows only.
\*   - recent_messages[s]  : the priors of the NEXT message s will send.
\*
\* recent_messages is the only new state.  It starts empty; receiving x adds x
\* and drops the priors of x, which x now dominates; sending y replaces it
\* wholesale with {y}, since y dominates everything s knew or had sent.  So it
\* is maintained as the maximal antichain of "everything s knows or has itself
\* sent" -- see CRecentIsMax / CRecentClosure below -- which is exactly the
\* CANONICAL priors field for the next message.  (CFilterOut no longer demands
\* m.priors = CRefs(m) -- canonicality is not memo-checkable -- but safe
\* acceptors still always SEND canonically: CSafeSentCanonical below.)
\*
\* Each safe acceptor s is modeled as one process PER (s, x) PAIR it might ever
\* receive.  That process's single step does three things atomically:
\*   1. Learn message x from the Msgs, provided s already knows every message in
\*      TranExclusive(x) (its whole prior history).  Guard verbatim from
\*      HPaxosPlusCal.
\*   2. Update recent_messages[s] as above.
\*   3. Forced send: build the one record s could possibly sign next --
\*      [sender |-> s, payload |-> the reply payload, priors |-> recent] --
\*      and send it iff it is CWellFormed.
\*
\* Step 3 replaces HPaxosPlusCal's "if some y with TranExclusive(y) = T exists,
\* send the CHOOSEn one".  The two agree exactly (CForcedSendAgrees below): the
\* history T pins down priors to the unique maximal antichain of T, and a safe
\* acceptor never signs a proposal, so the payload is forced to CReply's single
\* element.  Nothing is left to CHOOSE -- the candidate is a closed term, and
\* the abstract existential becomes a CWellFormed test on it.
\*
\* THE ONE DEVIATION from a naive transcription is in the recent_messages
\* update, which SKIPS any x that is already accounted for:
\*
\*     IF x \in known_messages[s] \/ Sig(x) = s
\*       THEN recent
\*       ELSE (recent \cup {x}) \ x.priors
\*
\* Both disjuncts say the same thing -- x is already in known \cup CSelfSent, so
\* learning it does not move that set, and the antichain over it must not move
\* either.  x \in known_messages[s] covers a RE-receipt; Sig(x) = s covers the
\* first receipt of one of s's OWN sends.  Note the step is still taken in both
\* cases: known_messages[s] still gains x and the forced send still runs, so
\* nothing HPaxosPlusCal can do is lost.  Only recent_messages stands still.
\*
\* The guards are VERBATIM from HPaxosPlusCal -- deliberately.  It is tempting
\* to guard out the re-receipt as "just stuttering", but it is NOT: on a
\* re-receipt HPaxosPlusCal recomputes T = (known \cup {x}) \cup CSelfSent, and
\* CSelfSent has GROWN since the first receipt fired a send.  So T becomes
\* T1 \cup {y1} and a further message y2, with priors {y1}, may legitimately be
\* sent.  Guarding the re-receipt away would delete those transitions and break
\* the equivalence.  The skip above is what makes the re-receipt come out right
\* instead: recent stays {y1}, so the candidate built is exactly y2.
\*
\* On the remaining branch -- x \notin known_messages[s] and Sig(x) # s -- the
\* subtraction is exact.  x is new to known \cup CSelfSent, and it is MAXIMAL
\* there: anything dominating x would have had x in its own history, and would
\* therefore have forced x into known_messages[s] before it could itself be
\* received or sent.  And the elements of recent that x dominates are precisely
\* recent \cap x.priors -- a z \in recent below x but below no DIRECT prior of x
\* cannot exist, since that prior is in known_messages[s] and would already have
\* knocked z out of the antichain.
\*
\* Byzantine senders (Senders \ SafeAcceptors) are UNCHANGED from HPaxosPlusCal:
\* they ignore known_messages and recent_messages entirely, and at any time may
\* send ANY message they sign whose exclusive history is already fully in the
\* Msgs.  They must stay unconstrained -- equivocation (two messages with the
\* same priors) is what CaughtS detects, and routing them through
\* recent_messages would make it unreachable.  This is any non-safe sender, not
\* just non-safe acceptors -- e.g. it also covers proposers behaving
\* adversarially.
\*
\* This module EXTENDS HPaxosPlusCal, so Msgs and known_messages here ARE
\* HPaxosPlusCal's variables and SafeAcceptors / LiveAcceptors / ByzSenders are
\* its constants -- the two specs constrain the same state and range over the
\* same processes, which is what makes HPaxosPlusCalConcreteEquiv statable.
\* It has to be EXTENDS rather than INSTANCE: tlapm cannot elaborate
\* INSTANCE HPaxosPlusCal at all (it dies with Expr.Levels: ARITY on
\* MessageInterface's CombinedFreshQdLrnsIdR), so the concrete definitions carry
\* a C prefix to avoid colliding with the abstract ones.
\*
\* MessageConcrete is EXTENDS (not LOCAL INSTANCE), and re-exports
\* MessageInterface as the SAME copy: the definitions below have bodies
\* mentioning operators of both, and every consumer that unfolds one of them
\* must see that same copy.  LOCAL INSTANCE would hand this module private
\* copies and consumer proofs would fail on renamed-apart operators.
EXTENDS HPaxosPlusCal, MessageConcrete

\* The identification this whole development runs under: every abstract
\* operator below (Messages, Proposals, Sig, Tran, TranExclusive, Refs, ...) IS
\* its Concrete-land counterpart.  MessageConcrete discharges
\* MessageInterfaceAssumptions for CMI, so it is consistent.
\*
\* It is a DEFINITION, not a module-level ASSUME: every lemma that needs it
\* carries it as an explicit hypothesis, exactly as the rest of this directory
\* treats SafeAcceptorsAssumption / LearnerGraphAssumptions / etc.  Nothing here
\* is a global axiom, so a theorem's ASSUME list is the whole truth about what
\* it depends on.
ConcreteMessageInterface == MessageInterface = CMI

\* SafeAcceptors, LiveAcceptors, their assumptions, and ByzSenders all arrive
\* from HPaxosPlusCal -- this module deliberately shares them rather than
\* re-declaring, so the two specs range over the very same processes.

(* --algorithm HPaxosPlusCalConcrete {
     variables
       Msgs = {},
       known_messages = [s \in SafeAcceptors |-> {}],
       recent_messages = [s \in SafeAcceptors |-> {}];

     \* One process per (safe acceptor, message) PAIR: whenever that message's
     \* whole prior history is already known to that acceptor, learn it (and
     \* forced-send).  Indexing by the pair -- rather than one process per
     \* acceptor with an internal `with` over the message -- means weak fairness
     \* can be imposed directly on each (acceptor, message) process (see
     \* CNetworkAssumption), with no separate operator needed to relate the
     \* fairness action to the system's step relation.
     \* self[1] is the acceptor; self[2] is the message.
     process (CSafeStep \in SafeAcceptors \times Messages)
     {
       lstep:
         while (TRUE) {
           when self[2] \in Msgs;
           when TranExclusive(self[2]) \subseteq known_messages[self[1]];
           \* rm is computed BEFORE known_messages is updated -- the test
           \* self[2] \in known_messages[self[1]] must read the PRE-state, and
           \* PlusCal statements see each other's assignments in order.
           \* Add self[2] and drop the priors it dominates -- self[2].priors =
           \* Refs(self[2]) by CFilterOut -- unless self[2] is already in
           \* known \cup CSelfSent, in which case the antichain does not move.
           with (rm = IF \/ self[2] \in known_messages[self[1]]
                         \/ Sig(self[2]) = self[1]
                        THEN recent_messages[self[1]]
                        ELSE (recent_messages[self[1]] \cup {self[2]})
                               \ self[2].priors) {
             \* The one record self[1] could sign next.  It is in CMC already:
             \* rm is a finite subset of Msgs \subseteq CMessages \subseteq CMC.
             \* A safe acceptor never signs a proposal, and CReply is the
             \* singleton {[type |-> "reply"]}, so the payload is forced.
             with (cand = [sender  |-> self[1],
                           payload |-> [type |-> "reply"],
                           priors  |-> rm]) {
               known_messages[self[1]] := known_messages[self[1]] \cup {self[2]};
               \* Everything in CTranExcl(cand) lies in Msgs and is therefore
               \* already well formed, so CWellFormed(cand) alone decides
               \* cand \in CMessages -- and it is exactly HPaxosPlusCal's
               \* "does a y with TranExclusive(y) = T exist?" (CForcedSendAgrees).
               if (CWellFormed(cand)) {
                 Msgs := Msgs \cup {cand};
                 recent_messages[self[1]] := {cand};
               } else {
                 recent_messages[self[1]] := rm;
               }
             }
           }
         }
     }

     process (CByzStep \in ByzSenders)
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
\* BEGIN TRANSLATION
\* This is the PlusCal output with the five names that would collide against
\* the EXTENDS'd HPaxosPlusCal -- vars, ProcSet, Init, Next, Spec, plus the two
\* process actions -- renamed with a C prefix.  Msgs and known_messages are NOT
\* re-declared: they are HPaxosPlusCal's own variables, which is the whole point
\* (the two specs constrain literally the same state).
VARIABLE recent_messages

CVars == << Msgs, known_messages, recent_messages >>

CProcSet == (SafeAcceptors \times Messages) \cup (ByzSenders)

CInit == (* Global variables *)
        /\ Msgs = {}
        /\ known_messages = [s \in SafeAcceptors |-> {}]
        /\ recent_messages = [s \in SafeAcceptors |-> {}]

CSafeStep(self) ==
  /\ self[2] \in Msgs
  /\ TranExclusive(self[2]) \subseteq known_messages[self[1]]
  /\ known_messages' = [known_messages EXCEPT
                          ![self[1]] = known_messages[self[1]] \cup {self[2]}]
  \* known_messages below is UNPRIMED: the test reads the pre-state.
  /\ LET rm   == IF \/ self[2] \in known_messages[self[1]]
                    \/ Sig(self[2]) = self[1]
                   THEN recent_messages[self[1]]
                   ELSE (recent_messages[self[1]] \cup {self[2]})
                          \ self[2].priors
         cand == [sender  |-> self[1],
                  payload |-> [type |-> "reply"],
                  priors  |-> rm]
     IN  IF CWellFormed(cand)
           THEN /\ Msgs' = Msgs \cup {cand}
                /\ recent_messages' = [recent_messages EXCEPT
                                         ![self[1]] = {cand}]
           ELSE /\ Msgs' = Msgs
                /\ recent_messages' = [recent_messages EXCEPT
                                         ![self[1]] = rm]

CByzStep(self) ==
  /\ \E y \in {z \in Messages : Sig(z) = self /\ TranExclusive(z) \subseteq Msgs}:
       Msgs' = (Msgs \cup {y})
  /\ UNCHANGED << known_messages, recent_messages >>

CNext == (\E self \in SafeAcceptors \times Messages: CSafeStep(self))
           \/ (\E self \in ByzSenders: CByzStep(self))

CSpec == CInit /\ [][CNext]_CVars

\* END TRANSLATION


\* ===================================================================
\* Per-message fairness
\* ===================================================================
\* Each live acceptor's learn step for each individual message is weakly fair:
\* if learning a particular x stays continuously enabled, it must eventually
\* happen.  Weak fairness on CSafeStep(self) as a whole
\* (a `fair process` annotation, self ranging only over acceptors) would only
\* force SOME learn step of each acceptor, not the learn of a PARTICULAR
\* message -- a live acceptor could be starved of one x forever while it keeps
\* learning others.  Imposing WF per (acceptor, message) pair, restricted to
\* LiveAcceptors, is exactly what we need.
CNetworkAssumption == \A self \in LiveAcceptors \times Messages : WF_CVars(CSafeStep(self))


\* ===================================================================
\* Inductive invariant
\* ===================================================================
\* HPaxosPlusCal's Inv, plus typing and containment for the new variable.
CInv ==
  /\ Msgs \in SUBSET Messages
  /\ known_messages \in [SafeAcceptors -> SUBSET Messages]
  /\ recent_messages \in [SafeAcceptors -> SUBSET Messages]
  /\ IsFiniteSet(Msgs)
  /\ \A s \in SafeAcceptors : known_messages[s] \subseteq Msgs
  /\ \A s \in SafeAcceptors : recent_messages[s] \subseteq Msgs
  /\ \A z \in Msgs : TranExclusive(z) \subseteq Msgs


\* ===================================================================
\* Bridge to HPaxosPlusCal
\* ===================================================================
\* CSelfSent(s) is the set HPaxosPlusCal's forced-send folds into its T: what s
\* has sent, as opposed to what it has been told.
CSelfSent(s) == {m \in Msgs : Sig(m) = s}

\* recent_messages[s] is precisely the maximal antichain of everything s knows
\* or has sent.  This is the invariant that makes the two specs line up, and it
\* is what "recent_messages represents the priors of the next message" means
\* formally: the candidate s builds carries CRefs -- the maximal elements of
\* its own history -- as its priors, even though CWellFormed no longer forces
\* that of every message.
CRecentIsMax ==
  \A s \in SafeAcceptors :
    recent_messages[s] = CMMax(known_messages[s] \cup CSelfSent(s))

\* recent_messages is not free state: it is pinned, at every instant, to a
\* function of Msgs and known_messages alone.  This is the refinement mapping
\* that witnesses the converse -- Spec cannot constrain recent_messages, but
\* Spec /\ []CRecentOK is exactly CSpec (HPaxosPlusCalConcreteSpecEquivalence).
\* The typing conjunct is load-bearing: CRecentIsMax alone fixes
\* recent_messages pointwise on SafeAcceptors and says nothing about the
\* function's domain, which the EXCEPT-equalities in the step proofs need.
CRecentOK ==
  /\ recent_messages \in [SafeAcceptors -> SUBSET Messages]
  /\ CRecentIsMax


\* ===================================================================
\* The pieces of a safe-acceptor step, named
\* ===================================================================
\* These mirror the LET inside CSafeStep exactly.  Naming them lets the step
\* equivalence be stated as "abstract action AND recent_messages' is this".
CRM(s, x) == IF \/ x \in known_messages[s]
                \/ Sig(x) = s
               THEN recent_messages[s]
               ELSE (recent_messages[s] \cup {x}) \ x.priors

CCand(s, x) == [sender  |-> s,
                payload |-> [type |-> "reply"],
                priors  |-> CRM(s, x)]

CRecentUpdate(s, x) ==
  IF CWellFormed(CCand(s, x))
    THEN [recent_messages EXCEPT ![s] = {CCand(s, x)}]
    ELSE [recent_messages EXCEPT ![s] = CRM(s, x)]

\* HPaxosPlusCal's forced-send target set.  Its own T is written over
\* known_messages', which the step sets to known_messages[s] \cup {x}.
CAT(s, x) == (known_messages[s] \cup {x}) \cup CSelfSent(s)


\* ===================================================================
\* Canonicality of safe sends
\* ===================================================================
\* Every message a safe acceptor has ever sent carries exactly its refs as its
\* priors.  Well-formedness no longer forces this of arbitrary (byz-sent)
\* messages -- it is not decidable from memos -- but the record a safe
\* acceptor BUILDS always has it, so it is an invariant of CSpec
\* (CSafeSentCanonicalHolds), and it is the third leg of the refinement
\* mapping in HPaxosPlusCalConcreteSpecEquivalence: it pins the abstract
\* spec's nondeterministic forced-send witness to the built record.
CSafeSentCanonical ==
  \A m \in Msgs : Sig(m) \in SafeAcceptors => m.priors = Refs(m)

\* ===================================================================
\* Equivalence target
\* ===================================================================
\* The crux: on a state where a learn step is enabled, the record this module
\* builds is well formed exactly when HPaxosPlusCal's forced-send has a
\* witness; it is then ITSELF a witness; and it is the only CANONICAL witness.
\* Given this -- plus CSafeSentCanonical pinning the abstract choice -- the
\* two safe-acceptor actions assign the same Msgs' and the same
\* known_messages', so the specs agree on (Msgs, known_messages) and this
\* module merely carries recent_messages along.  The guards and the
\* known_messages assignment are syntactically identical, and the byz actions
\* are too, so this is the whole content of the equivalence.
\*
\* Stated at ONE pair rather than as a \A over SafeAcceptors \X Messages: it is
\* only ever needed, and only ever provable, at pairs passing the receive guard,
\* and the pointwise form keeps instantiation first-order.
CForcedSendAgreesAt(s, x) ==
  /\ CWellFormed(CCand(s, x))
       <=> (\E y \in (Messages \ Proposals) :
              Sig(y) = s /\ TranExclusive(y) = CAT(s, x))
  /\ CWellFormed(CCand(s, x)) =>
       /\ CCand(s, x) \in (Messages \ Proposals)
       /\ Sig(CCand(s, x)) = s
       /\ TranExclusive(CCand(s, x)) = CAT(s, x)
  /\ \A y \in (Messages \ Proposals) :
       (Sig(y) = s /\ TranExclusive(y) = CAT(s, x) /\ y.priors = Refs(y))
         => y = CCand(s, x)


\* ===================================================================
\* The joint inductive invariant
\* ===================================================================
\* Shorthand for "everything s knows or has sent".
UOf(s) == known_messages[s] \cup CSelfSent(s)

\* KnownTranClosureInvT and SelfSentBoundedInvT are HPaxosPlusCal's OWN
\* auxiliary invariants; they cannot be inherited from the abstract development
\* when proving CSpec => Spec, because inheriting them would need CNext => Next,
\* which needs the forced-send agreement, which needs this invariant.  So all
\* four are carried through CNext together.
CJoint ==
  /\ CInv
  /\ KnownTranClosureInvT
  /\ SelfSentBoundedInvT
  /\ CRecentIsMax
====================================================================
