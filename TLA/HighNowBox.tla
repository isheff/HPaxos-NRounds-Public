------------------------------ MODULE HighNowBox ------------------------------
EXTENDS HPaxosPlusCal, AllMsgNetElem
LOCAL INSTANCE TLAPS

\* Producer of []HighNowT from the theorem-level relaxed-uniqueness hypothesis
\* over am (clone of UniqNowBox).
LEMMA HighNowBox ==
  ASSUME NEW am, NEW bal \in Ballots, NEW p \in Proposals,
         \A x \in am : ((IsProposal(x) /\ (B(x) > bal)) =>
           ((V(x) = V(p)) /\ ((B(x) < B(p)) \/ (x = p))))
  PROVE  Spec => (IsAllMessagesEverSent(am) => []HighNowT(p, bal))
<1>t1. Init => ((\A z : z \in Proposals => (((z \in Msgs) /\ (B(z) > bal)) =>
                          ((V(z) = V(p)) /\ ((B(z) < B(p)) \/ (z = p)))))
               <=> (\A z \in Proposals : ((z \in Msgs) /\ (B(z) > bal)) =>
                          ((V(z) = V(p)) /\ ((B(z) < B(p)) \/ (z = p)))))
  OBVIOUS
<1>t2. ((\A z : z \in Proposals => (((z \in Msgs) /\ (B(z) > bal)) =>
                  ((V(z) = V(p)) /\ ((B(z) < B(p)) \/ (z = p)))))
        <=> (\A z \in Proposals : ((z \in Msgs) /\ (B(z) > bal)) =>
                  ((V(z) = V(p)) /\ ((B(z) < B(p)) \/ (z = p))))) /\ [Next]_vars
       => ((\A z : z \in Proposals => (((z \in Msgs) /\ (B(z) > bal)) =>
                     ((V(z) = V(p)) /\ ((B(z) < B(p)) \/ (z = p)))))
           <=> (\A z \in Proposals : ((z \in Msgs) /\ (B(z) > bal)) =>
                     ((V(z) = V(p)) /\ ((B(z) < B(p)) \/ (z = p)))))'
  OBVIOUS
<1>taub. Spec => []((\A z : z \in Proposals => (((z \in Msgs) /\ (B(z) > bal)) =>
                              ((V(z) = V(p)) /\ ((B(z) < B(p)) \/ (z = p)))))
                    <=> (\A z \in Proposals : ((z \in Msgs) /\ (B(z) > bal)) =>
                              ((V(z) = V(p)) /\ ((B(z) < B(p)) \/ (z = p)))))
  BY <1>t1, <1>t2, PTL DEF Spec
<1>ub. \A z : Spec => (IsAllMessagesEverSent(am)
              => [](z \in Proposals => (((z \in Msgs) /\ (B(z) > bal)) =>
                       ((V(z) = V(p)) /\ ((B(z) < B(p)) \/ (z = p))))))
  <2> SUFFICES ASSUME NEW z
               PROVE  Spec => (IsAllMessagesEverSent(am)
                      => [](z \in Proposals => (((z \in Msgs) /\ (B(z) > bal)) =>
                               ((V(z) = V(p)) /\ ((B(z) < B(p)) \/ (z = p))))))
    OBVIOUS
  <2>amn. Spec => (IsAllMessagesEverSent(am) => AllMsgBoxOp(z, am))
    BY AllMsgNetElem
  <2>ax. Spec => (IsAllMessagesEverSent(am) => [](z \in Msgs => z \in am))
    BY <2>amn DEF AllMsgBoxOp
  <2>uq. (z \in Proposals /\ z \in am /\ B(z) > bal)
           => ((V(z) = V(p)) /\ ((B(z) < B(p)) \/ (z = p)))
    BY DEF IsProposal
  <2>rA. [](z \in am) \/ []( ~(z \in am))  OBVIOUS
  <2>rB. [](B(z) > bal) \/ []( ~(B(z) > bal))  OBVIOUS
  <2>rP. [](z \in Proposals) \/ []( ~(z \in Proposals))  OBVIOUS
  <2>rV. [](V(z) = V(p)) \/ []( ~(V(z) = V(p)))  OBVIOUS
  <2>rL. [](B(z) < B(p)) \/ []( ~(B(z) < B(p)))  OBVIOUS
  <2>rE. [](z = p) \/ []( ~(z = p))  OBVIOUS
  <2> QED  BY <2>ax, <2>uq, <2>rA, <2>rB, <2>rP, <2>rV, <2>rL, <2>rE, PTL
<1> SUFFICES ASSUME Spec, IsAllMessagesEverSent(am)
             PROVE  []HighNowT(p, bal)
  OBVIOUS
<1>ub2. \A z : [](z \in Proposals => (((z \in Msgs) /\ (B(z) > bal)) =>
                     ((V(z) = V(p)) /\ ((B(z) < B(p)) \/ (z = p)))))
  BY <1>ub
<1>eq. (\A z : [](z \in Proposals => (((z \in Msgs) /\ (B(z) > bal)) =>
                     ((V(z) = V(p)) /\ ((B(z) < B(p)) \/ (z = p))))))
       <=> ([](\A z : z \in Proposals => (((z \in Msgs) /\ (B(z) > bal)) =>
                     ((V(z) = V(p)) /\ ((B(z) < B(p)) \/ (z = p))))))
  OBVIOUS
<1>rhs. [](\A z : z \in Proposals => (((z \in Msgs) /\ (B(z) > bal)) =>
                     ((V(z) = V(p)) /\ ((B(z) < B(p)) \/ (z = p)))))
  BY <1>ub2, <1>eq
<1>taub2. []((\A z : z \in Proposals => (((z \in Msgs) /\ (B(z) > bal)) =>
                        ((V(z) = V(p)) /\ ((B(z) < B(p)) \/ (z = p)))))
             <=> (\A z \in Proposals : ((z \in Msgs) /\ (B(z) > bal)) =>
                        ((V(z) = V(p)) /\ ((B(z) < B(p)) \/ (z = p)))))
  BY <1>taub
<1>conv. [](\A z \in Proposals : ((z \in Msgs) /\ (B(z) > bal)) =>
                        ((V(z) = V(p)) /\ ((B(z) < B(p)) \/ (z = p))))
  BY <1>rhs, <1>taub2, PTL
<1> QED  BY <1>conv DEF HighNowT
====================================================================
