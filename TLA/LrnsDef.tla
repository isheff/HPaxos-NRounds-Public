----------------------------- MODULE LrnsDef -----------------------------
EXTENDS MessageInterface, CombinedFreshQdLrnsIdRec

\* The lrns field records the learners alpha whose depth-1 quorum
\* (SigS(Qd(.,.,1))) is a quorum -- exactly HasDepth(alpha, m, 1).
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
====================================================================
