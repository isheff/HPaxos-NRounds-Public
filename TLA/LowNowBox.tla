------------------------------ MODULE LowNowBox ------------------------------
EXTENDS HPaxosPlusCal, AllMsgNetElem
LOCAL INSTANCE TLAPS

LEMMA LowNowBox ==
  ASSUME NEW allmessages, NEW bal \in Ballots,
         NEW M, M = {mm \in allmessages : B(mm) <= bal}
  PROVE  Spec => (IsAllMessagesEverSent(allmessages) => []LowNowT(bal, M))
<1>t1. Init => ((\A w : w \in Messages => ((w \in Msgs /\ B(w) <= bal) => (w \in M)))
               <=> (\A w \in Messages : ((w \in Msgs /\ B(w) <= bal) => (w \in M))))
  OBVIOUS
<1>t2. ((\A w : w \in Messages => ((w \in Msgs /\ B(w) <= bal) => (w \in M)))
        <=> (\A w \in Messages : ((w \in Msgs /\ B(w) <= bal) => (w \in M)))) /\ [Next]_vars
       => ((\A w : w \in Messages => ((w \in Msgs /\ B(w) <= bal) => (w \in M)))
           <=> (\A w \in Messages : ((w \in Msgs /\ B(w) <= bal) => (w \in M))))'
  OBVIOUS
<1>taub. Spec => []((\A w : w \in Messages => ((w \in Msgs /\ B(w) <= bal) => (w \in M)))
                    <=> (\A w \in Messages : ((w \in Msgs /\ B(w) <= bal) => (w \in M))))
  BY <1>t1, <1>t2, PTL DEF Spec
<1>ub. \A w : Spec => (IsAllMessagesEverSent(allmessages)
              => [](w \in Messages => ((w \in Msgs /\ B(w) <= bal) => (w \in M))))
  <2> SUFFICES ASSUME NEW w
               PROVE  Spec => (IsAllMessagesEverSent(allmessages)
                      => [](w \in Messages => ((w \in Msgs /\ B(w) <= bal) => (w \in M))))
    OBVIOUS
  <2>amn. Spec => (IsAllMessagesEverSent(allmessages) => AllMsgBoxOp(w, allmessages))
    BY AllMsgNetElem
  <2>ax. Spec => (IsAllMessagesEverSent(allmessages) => [](w \in Msgs => w \in allmessages))
    BY <2>amn DEF AllMsgBoxOp
  <2>uq. (w \in allmessages /\ B(w) <= bal) => (w \in M)  OBVIOUS
  <2>rA. [](w \in allmessages) \/ []( ~(w \in allmessages))  OBVIOUS
  <2>rB. [](B(w) <= bal) \/ []( ~(B(w) <= bal))  OBVIOUS
  <2>rM. [](w \in Messages) \/ []( ~(w \in Messages))  OBVIOUS
  <2>rN. [](w \in M) \/ []( ~(w \in M))  OBVIOUS
  <2> QED  BY <2>ax, <2>uq, <2>rA, <2>rB, <2>rM, <2>rN, PTL
<1> SUFFICES ASSUME Spec, IsAllMessagesEverSent(allmessages)
             PROVE  []LowNowT(bal, M)
  OBVIOUS
<1>ub2. \A w : [](w \in Messages => ((w \in Msgs /\ B(w) <= bal) => (w \in M)))
  BY <1>ub
<1>eq. (\A w : [](w \in Messages => ((w \in Msgs /\ B(w) <= bal) => (w \in M))))
       <=> ([](\A w : w \in Messages => ((w \in Msgs /\ B(w) <= bal) => (w \in M))))
  OBVIOUS
<1>rhs. [](\A w : w \in Messages => ((w \in Msgs /\ B(w) <= bal) => (w \in M)))
  BY <1>ub2, <1>eq
<1>taub2. []((\A w : w \in Messages => ((w \in Msgs /\ B(w) <= bal) => (w \in M)))
             <=> (\A w \in Messages : ((w \in Msgs /\ B(w) <= bal) => (w \in M))))
  BY <1>taub
<1>conv. [](\A w \in Messages : ((w \in Msgs /\ B(w) <= bal) => (w \in M)))
  BY <1>rhs, <1>taub2, PTL
<1> QED  BY <1>conv DEF LowNowT
====================================================================
