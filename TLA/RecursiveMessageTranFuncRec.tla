------------------- MODULE RecursiveMessageTranFuncRec -------------------
\*   MessageInterface -> RecursiveMessageTranFunc, TranExclusive, Messages
\*   TranSubMessages, TranExclusiveDecreasesTranSize, GFunRecMI, RMTFViaG
\*                    -> cited lemmas; each shares MessageInterface with this
\*                       module, so all must be EXTENDS rather than INSTANCE.
EXTENDS MessageInterface,
        TranSubMessages, TranExclusiveDecreasesTranSize,
        GFunRecMI, RMTFViaG

THEOREM RecursiveMessageTranFuncRec ==
    ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
           NEW m \in Messages,
           NEW F(_,_)
    PROVE RecursiveMessageTranFunc(F, m) =
          F(m, {RecursiveMessageTranFunc(F, x) : x \in TranExclusive(m)})
<1>h1. \A x \in Messages : TranExclusive(x) \subseteq Messages
  BY TranSubMessages DEF TranExclusive
<1>h2. \A x \in Messages : \A y \in TranExclusive(x) :
         Cardinality(Tran(y)) < Cardinality(Tran(x))
  BY TranExclusiveDecreasesTranSize
<1>1. GFunMI(F, TranExclusive)[Cardinality(Tran(m))][m]
        = F(m, {GFunMI(F, TranExclusive)[Cardinality(Tran(x))][x] : x \in TranExclusive(m)})
  BY <1>h1, <1>h2, GFunRecMI
<1>2. RecursiveMessageTranFunc(F, m) = GFunMI(F, TranExclusive)[Cardinality(Tran(m))][m]
  BY RMTFViaG
<1>3. {GFunMI(F, TranExclusive)[Cardinality(Tran(x))][x] : x \in TranExclusive(m)}
      = {RecursiveMessageTranFunc(F, x) : x \in TranExclusive(m)}
  BY RMTFViaG
<1> QED BY <1>1, <1>2, <1>3
====================================================================
