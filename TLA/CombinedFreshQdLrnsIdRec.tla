------------------- MODULE CombinedFreshQdLrnsIdRec -------------------
EXTENDS MessageInterface, RecursiveMessageTranFuncRec

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
====================================================================
