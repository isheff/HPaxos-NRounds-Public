--------------------------- MODULE EventuallyCaught ---------------------------
\* Equivocation is eventually detected by EVERYONE live: if an acceptor x has
\* sent two messages m1, m2 with neither in the other's transitive history (the
\* CaughtS fork pattern), and each of them is known to SOME live acceptor, then
\* eventually EVERY live acceptor y has both -- and hence x is caught in y's own
\* knowledge, x \in CaughtS(known_messages[y]).
\*
\* Note the hypotheses ask only that each witness reach some live acceptor
\* (possibly different ones): under the weakened NetworkAssumption a
\* known-to-live message is live-relevant, so the eventual-knowledge chain
\* (EventuallyKnown) spreads both witnesses to every live acceptor.  That the
\* witnesses are SENT (m1, m2 \in Msgs) follows from being known (Inv).
EXTENDS HPaxosPlusCal, AlwaysEventuallyKnownInvariant, EKExtract, InvHolds
LOCAL INSTANCE TLAPS

THEOREM EventuallyCaught ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions, AcceptorsAssumptions,
         NEW x \in Acceptors, NEW m1 \in Messages, NEW m2 \in Messages,
         Sig(m1) = x, Sig(m2) = x,
         m1 \notin Tran(m2), m2 \notin Tran(m1)
  PROVE  (Spec /\ NetworkAssumption) =>
           ((KnownToLive(m1) /\ KnownToLive(m2))
             ~> (\A y \in LiveAcceptors : x \in CaughtS(known_messages[y])))
<1>msub. {m1, m2} \in SUBSET Messages  OBVIOUS
\* Spec => [](...) side facts, proven while no raw-temporal hypothesis is
\* ambient (NetworkAssumption would silently disable PTL's necessitation).
<1>relb. Spec => []((KnownToLive(m1) /\ KnownToLive(m2))
                    => {m1, m2} \subseteq RelevantMsgs)
  <2>1. Inv /\ KnownToLive(m1) /\ KnownToLive(m2) => {m1, m2} \subseteq RelevantMsgs
    BY DEF Inv, KnownToLive, RelevantMsgs, LiveRelevant,
           AcceptorsAssumptions, LiveAcceptorsAssumption
  <2>2. Spec => []Inv  BY InvHolds
  <2> QED  BY <2>1, <2>2, PTL DEF Spec
<1>tgtb. Spec => []((\A a \in LiveAcceptors : {m1, m2} \subseteq known_messages[a])
                    => (\A y \in LiveAcceptors : x \in CaughtS(known_messages[y])))
  <2>1. Init => ((\A a \in LiveAcceptors : {m1, m2} \subseteq known_messages[a])
                 => (\A y \in LiveAcceptors : x \in CaughtS(known_messages[y])))
    BY DEF CaughtS
  <2>2. ((\A a \in LiveAcceptors : {m1, m2} \subseteq known_messages[a])
         => (\A y \in LiveAcceptors : x \in CaughtS(known_messages[y]))) /\ [Next]_vars
        => ((\A a \in LiveAcceptors : {m1, m2} \subseteq known_messages[a])
            => (\A y \in LiveAcceptors : x \in CaughtS(known_messages[y])))'
    BY DEF CaughtS
  <2> QED  BY <2>1, <2>2, PTL DEF Spec
<1> SUFFICES ASSUME Spec, NetworkAssumption
             PROVE  (KnownToLive(m1) /\ KnownToLive(m2))
                      ~> (\A y \in LiveAcceptors : x \in CaughtS(known_messages[y]))
  OBVIOUS
<1>ekinv. []EventuallyKnownInvariant  BY AlwaysEventuallyKnownInvariant
<1>ekl. EKLT({m1, m2})  BY <1>ekinv, <1>msub, EKExtract
<1>ek. ({m1, m2} \subseteq RelevantMsgs)
         ~> (\A a \in LiveAcceptors : {m1, m2} \subseteq known_messages[a])
  BY <1>ekl DEF EKLT
<1>relbb. []((KnownToLive(m1) /\ KnownToLive(m2)) => {m1, m2} \subseteq RelevantMsgs)
  BY <1>relb
<1>tgtbb. []((\A a \in LiveAcceptors : {m1, m2} \subseteq known_messages[a])
             => (\A y \in LiveAcceptors : x \in CaughtS(known_messages[y])))
  BY <1>tgtb
<1> QED  BY <1>ek, <1>relbb, <1>tgtbb, PTL
=============================================================================
