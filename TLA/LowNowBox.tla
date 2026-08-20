------------------------------ MODULE LowNowBox ------------------------------
EXTENDS HPaxosPlusCal, AllMsgRelElem
LOCAL INSTANCE TLAPS

\* Ever-known flavour: every LIVE-RELEVANT sent message with ballot <= bal is
\* in M (the low part of the ever-known set).
LEMMA LowNowBox ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions, AcceptorsAssumptions,
         LiveAcceptors # {},
         NEW allmessages, NEW bal \in Ballots,
         NEW M, M = {mm \in allmessages : B(mm) <= bal}
  PROVE  (Spec /\ NetworkAssumption)
           => (IsAllMessagesEverKnown(allmessages) => []LowNowT(bal, M))
<1>t1. Init => ((\A w : w \in Messages => ((w \in RelevantMsgs /\ B(w) <= bal) => (w \in M)))
               <=> (\A w \in Messages : ((w \in RelevantMsgs /\ B(w) <= bal) => (w \in M))))
  OBVIOUS
<1>t2. ((\A w : w \in Messages => ((w \in RelevantMsgs /\ B(w) <= bal) => (w \in M)))
        <=> (\A w \in Messages : ((w \in RelevantMsgs /\ B(w) <= bal) => (w \in M)))) /\ [Next]_vars
       => ((\A w : w \in Messages => ((w \in RelevantMsgs /\ B(w) <= bal) => (w \in M)))
           <=> (\A w \in Messages : ((w \in RelevantMsgs /\ B(w) <= bal) => (w \in M))))'
  OBVIOUS
<1>taub0. Spec => []((\A w : w \in Messages => ((w \in RelevantMsgs /\ B(w) <= bal) => (w \in M)))
                    <=> (\A w \in Messages : ((w \in RelevantMsgs /\ B(w) <= bal) => (w \in M))))
  BY <1>t1, <1>t2, PTL DEF Spec
<1>ub. \A w : (Spec /\ NetworkAssumption) => (IsAllMessagesEverKnown(allmessages)
              => [](w \in Messages => ((w \in RelevantMsgs /\ B(w) <= bal) => (w \in M))))
  <2> SUFFICES ASSUME NEW w
               PROVE  (Spec /\ NetworkAssumption) => (IsAllMessagesEverKnown(allmessages)
                      => [](w \in Messages => ((w \in RelevantMsgs /\ B(w) <= bal) => (w \in M))))
    OBVIOUS
  <2>amn. (Spec /\ NetworkAssumption)
            => (IsAllMessagesEverKnown(allmessages) => RelAllBoxOp(w, allmessages))
    BY AllMsgRelElem
  <2>ax. (Spec /\ NetworkAssumption)
           => (IsAllMessagesEverKnown(allmessages) => [](w \in RelevantMsgs => w \in allmessages))
    BY <2>amn DEF RelAllBoxOp
  <2>uq. (w \in allmessages /\ B(w) <= bal) => (w \in M)  OBVIOUS
  <2>rA. [](w \in allmessages) \/ []( ~(w \in allmessages))  OBVIOUS
  <2>rB. [](B(w) <= bal) \/ []( ~(B(w) <= bal))  OBVIOUS
  <2>rM. [](w \in Messages) \/ []( ~(w \in Messages))  OBVIOUS
  <2>rN. [](w \in M) \/ []( ~(w \in M))  OBVIOUS
  <2> QED  BY <2>ax, <2>uq, <2>rA, <2>rB, <2>rM, <2>rN, PTL
<1> SUFFICES ASSUME Spec, NetworkAssumption, IsAllMessagesEverKnown(allmessages)
             PROVE  []LowNowT(bal, M)
  OBVIOUS
<1>taub. []((\A w : w \in Messages => ((w \in RelevantMsgs /\ B(w) <= bal) => (w \in M)))
             <=> (\A w \in Messages : ((w \in RelevantMsgs /\ B(w) <= bal) => (w \in M))))
  BY <1>taub0
<1>ub2. \A w : [](w \in Messages => ((w \in RelevantMsgs /\ B(w) <= bal) => (w \in M)))
  BY <1>ub
<1>eq. (\A w : [](w \in Messages => ((w \in RelevantMsgs /\ B(w) <= bal) => (w \in M))))
       <=> ([](\A w : w \in Messages => ((w \in RelevantMsgs /\ B(w) <= bal) => (w \in M))))
  OBVIOUS
<1>rhs. [](\A w : w \in Messages => ((w \in RelevantMsgs /\ B(w) <= bal) => (w \in M)))
  BY <1>ub2, <1>eq
<1>conv. [](\A w \in Messages : ((w \in RelevantMsgs /\ B(w) <= bal) => (w \in M)))
  BY <1>rhs, <1>taub, PTL
<1> QED  BY <1>conv DEF LowNowT
====================================================================
