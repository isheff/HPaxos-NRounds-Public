------------------ MODULE SafeAcceptorsNeverCaughtInfinite ------------------
EXTENDS HPaxosPlusCal, FiniteSetTheorems, FiniteDiamond,
        NeverCaughtStep, BridgeUncaught, DiaBoxAtomContra,
        AlwaysSafeAcceptorsUncaughtInvariant, KnownDiaMem
LOCAL INSTANCE TLAPS

\* corollary of AlwaysSafeAcceptorsUncaughtInvariant: if some SafeAcceptor s were
\* caught by the (infinite) set of all-ever-sent messages, then the two messages
\* m1,m2 that catch it are each eventually known, hence eventually in Msgs
\* (KnownDiaMem);
\* being finite they are eventually BOTH in Msgs at once (FiniteDiamond), at
\* which state s is caught in Msgs -- contradicting AlwaysSafeAcceptorsUncaught.
LEMMA SafeAcceptorsNeverCaughtInfinite ==
  \A allmessages : \* all messages eventually sent
  (/\ Spec
   /\ MessageInterfaceAssumptions
   /\ ValueInterfaceAssumptions
   /\ LearnerGraphAssumptions
   /\ AcceptorsAssumptions
   /\ IsAllMessagesEverKnown(allmessages)
  ) => (SafeAcceptors \cap CaughtS(allmessages)) = {}
<1> SUFFICES ASSUME NEW allmessages,
                    Spec, MessageInterfaceAssumptions, ValueInterfaceAssumptions,
                    LearnerGraphAssumptions, AcceptorsAssumptions, IsAllMessagesEverKnown(allmessages)
             PROVE  (SafeAcceptors \cap CaughtS(allmessages)) = {}
  OBVIOUS
<1> SUFFICES ASSUME NEW s, s \in SafeAcceptors, s \in CaughtS(allmessages)
             PROVE  FALSE
  OBVIOUS
<1>ssafe. s \in SafeAcceptors  OBVIOUS
<1>sacc. s \in Acceptors  BY <1>ssafe DEF AcceptorsAssumptions, SafeAcceptorsAssumption
\* two forking same-signer witnesses in allmessages
<1> PICK m1 \in allmessages, m2 \in allmessages :
      Sig(m1)=s /\ Sig(m2)=s /\ m1 \notin Tran(m2) /\ m2 \notin Tran(m1)
  BY DEF CaughtS
<1>sg1. Sig(m1)=s  BY DEF CaughtS
<1>sg2. Sig(m2)=s  OBVIOUS
<1>nt1. m1 \notin Tran(m2)  OBVIOUS
<1>nt2. m2 \notin Tran(m1)  OBVIOUS
\* {m1,m2} is finite and eventually all in Msgs
<1>msub. {m1, m2} \subseteq allmessages  OBVIOUS
<1>mfin. IsFiniteSet({m1, m2})
  <2>1. IsFiniteSet({m1})  BY FS_Singleton
  <2>2. IsFiniteSet({m1} \cup {m2})  BY <2>1, FS_AddElement
  <2>3. {m1, m2} = {m1} \cup {m2}  OBVIOUS
  <2> QED  BY <2>2, <2>3
<1>mdia. \A m \in {m1, m2} : DiaMem(m)
  <2> SUFFICES ASSUME NEW m \in {m1, m2} PROVE DiaMem(m)  OBVIOUS
  <2>mx. m \in allmessages  BY <1>msub
  <2>1. Spec => (IsAllMessagesEverKnown(allmessages) => (m \in allmessages => DiaMem(m)))
    BY KnownDiaMem
  <2> QED  BY <2>mx, <2>1
<1>fdhyp. FD_Hyp({m1, m2})  BY <1>mfin, <1>mdia DEF FD_Hyp
<1>fdgood. FD_Good({m1, m2})  BY <1>fdhyp, FiniteDiamond
<1>ev. <>({m1, m2} \subseteq Msgs)  BY <1>fdgood DEF FD_Good, FD_Tgt
\* whenever {m1,m2} in Msgs, s is caught in Msgs
<1>nc. Spec => []({m1, m2} \subseteq Msgs => s \in CaughtS(Msgs))
  BY <1>sacc, <1>sg1, <1>sg2, <1>nt1, <1>nt2, NeverCaughtStep
<1>never2. []({m1, m2} \subseteq Msgs => s \in CaughtS(Msgs))  BY <1>nc
\* the safety invariant: s is never caught in Msgs
<1>inv. []SafeAcceptorsUncaughtInvariant  BY AlwaysSafeAcceptorsUncaughtInvariant
<1>bridge. Spec => [](SafeAcceptorsUncaughtInvariant => ~(s \in CaughtS(Msgs)))
  BY <1>ssafe, BridgeUncaught
<1>bridge2. [](SafeAcceptorsUncaughtInvariant => ~(s \in CaughtS(Msgs)))  BY <1>bridge
<1>notcaught. [](~(s \in CaughtS(Msgs)))  BY <1>inv, <1>bridge2, PTL
\* contradiction
<1>evc. <>(s \in CaughtS(Msgs))  BY <1>ev, <1>never2, PTL
<1> QED  BY <1>evc, <1>notcaught, DiaBoxAtomContra
====================================================================
