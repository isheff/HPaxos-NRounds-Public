---------------------------- MODULE DigestRec ----------------------------
\* Digest satisfies its defining recursion (mirrors CombinedFreshQdLrnsIdRec,
\* via the Refs-flavoured Rec theorem).
EXTENDS RecursiveWellFormed, RecursiveMessageRefsFuncRec

LEMMA DigestRec ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         NEW x \in Messages
  PROVE Digest(x) = DigestR(x, {Digest(p) : p \in Refs(x)})
<1>1. RecursiveMessageRefsFunc(DigestR, x)
        = DigestR(x, {RecursiveMessageRefsFunc(DigestR, p) : p \in Refs(x)})
  BY RecursiveMessageRefsFuncRec
<1> QED BY <1>1 DEF Digest
====================================================================
