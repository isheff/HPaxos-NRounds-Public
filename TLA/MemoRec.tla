---------------------------- MODULE MemoRec ----------------------------
\* Memo satisfies its defining recursion (mirrors CombinedFreshQdLrnsIdRec,
\* via the Refs-flavoured Rec theorem).
EXTENDS RecursiveWellFormed, RecursiveMessageRefsFuncRec

LEMMA MemoRec ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         NEW x \in Messages
  PROVE Memo(x) = MemoR(x, {Memo(p) : p \in Refs(x)})
<1>1. RecursiveMessageRefsFunc(MemoR, x)
        = MemoR(x, {RecursiveMessageRefsFunc(MemoR, p) : p \in Refs(x)})
  BY RecursiveMessageRefsFuncRec
<1> QED BY <1>1 DEF Memo
====================================================================
