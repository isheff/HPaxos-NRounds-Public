------------------- MODULE RecursiveMessageRefsFuncRec -------------------
\* Refs-flavoured twin of RecursiveMessageTranFuncRec; cites RMRFViaG rather
\* than RMTFViaG. All cited lemmas share MessageInterface, hence EXTENDS.
EXTENDS MessageInterface,
        TranSubMessages, TranExclusiveDecreasesTranSize,
        GFunRecMI, RMRFViaG

THEOREM RecursiveMessageRefsFuncRec ==
    ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
           NEW m \in Messages,
           NEW F(_,_)
    PROVE RecursiveMessageRefsFunc(F, m) =
          F(m, {RecursiveMessageRefsFunc(F, x) : x \in Refs(m)})
<1>sub. \A x \in Messages : Refs(x) \subseteq TranExclusive(x)
  BY DEF Refs
<1>h1. \A x \in Messages : Refs(x) \subseteq Messages
  BY <1>sub, TranSubMessages DEF TranExclusive
<1>h2. \A x \in Messages : \A y \in Refs(x) :
         Cardinality(Tran(y)) < Cardinality(Tran(x))
  BY <1>sub, TranExclusiveDecreasesTranSize
<1>1. GFunMI(F, Refs)[Cardinality(Tran(m))][m]
        = F(m, {GFunMI(F, Refs)[Cardinality(Tran(x))][x] : x \in Refs(m)})
  BY <1>h1, <1>h2, GFunRecMI
<1>2. RecursiveMessageRefsFunc(F, m) = GFunMI(F, Refs)[Cardinality(Tran(m))][m]
  BY RMRFViaG
<1>3. {GFunMI(F, Refs)[Cardinality(Tran(x))][x] : x \in Refs(m)}
      = {RecursiveMessageRefsFunc(F, x) : x \in Refs(m)}
  BY RMRFViaG
<1> QED BY <1>1, <1>2, <1>3
====================================================================
