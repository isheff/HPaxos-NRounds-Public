---------------- MODULE RecursiveMessageRefsFuncUnique ----------------
EXTENDS MessageInterface,
        TranSubMessages, TranExclusiveDecreasesTranSize, GFunLeastMI

THEOREM RecursiveMessageRefsFuncUnique ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic, NEW F(_,_), NEW H1(_), NEW H2(_),
         \A mm \in Messages : H1(mm) = F(mm, {H1(p) : p \in Refs(mm)}),
         \A mm \in Messages : H2(mm) = F(mm, {H2(p) : p \in Refs(mm)})
  PROVE \A mm \in Messages : H1(mm) = H2(mm)
<1>sub. \A x \in Messages : Refs(x) \subseteq TranExclusive(x)
  BY DEF Refs
<1>h1. \A x \in Messages : Refs(x) \subseteq Messages
  BY <1>sub, TranSubMessages DEF TranExclusive
<1>h2. \A x \in Messages : \A y \in Refs(x) :
         Cardinality(Tran(y)) < Cardinality(Tran(x))
  BY <1>sub, TranExclusiveDecreasesTranSize
<1>1. \A mm \in Messages : H1(mm) = GFunMI(F, Refs)[Cardinality(Tran(mm))][mm]
  BY <1>h1, <1>h2, GFunLeastMI
<1>2. \A mm \in Messages : H2(mm) = GFunMI(F, Refs)[Cardinality(Tran(mm))][mm]
  BY <1>h1, <1>h2, GFunLeastMI
<1> QED BY <1>1, <1>2
====================================================================
