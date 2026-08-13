--------------------------- MODULE PrevTranRec ---------------------------
\*   MemoRec, DeepestKnownInv -> cited lemmas
\*   TLAPS -> proof-only
EXTENDS RecursiveWellFormed, MemoRec, DeepestKnownInv
LOCAL INSTANCE TLAPS

\* PrevTran's defining recursion: m itself, plus the prevtran of the
\* deepestknown message for m's own signer, when there is one. The
\* canonicality conjunct of DeepestKnownInvariant turns the prevtran
\* stored in the entry's memo into PrevTran of the entry's message.
\* (Combined with DeepestKnownPrev, the chained message is in Prev(m).)
LEMMA PrevTranRec ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         NEW m \in Messages
  PROVE PrevTran(m)
          = {m} \cup (IF Sig(m) \in DOMAIN DeepestKnown(m)
                        THEN PrevTran(DeepestKnown(m)[Sig(m)][2].id)
                        ELSE {})
<1> DEFINE recs == {Memo(p) : p \in Refs(m)}
<1>unf. Memo(m) = MemoR(m, recs)  BY MemoRec
<1>pt. PrevTran(m) = PrevTranAssemble(m, recs)
  BY <1>unf DEF PrevTran, MemoR
<1>dk. DeepestKnown(m) = DeepestKnownAssemble(recs)
  BY <1>unf DEF DeepestKnown, MemoR
<1>a. CASE Sig(m) \in DOMAIN DeepestKnown(m)
  <2>inv. DeepestKnownInvariant(m)  BY DeepestKnownInv
  <2>can. DeepestKnown(m)[Sig(m)][2]
            = Memo(DeepestKnown(m)[Sig(m)][2].id)
    BY <2>inv, <1>a DEF DeepestKnownInvariant
  <2>ptz. DeepestKnown(m)[Sig(m)][2].prevtran
            = PrevTran(DeepestKnown(m)[Sig(m)][2].id)
    BY <2>can DEF PrevTran
  <2>1. PrevTranAssemble(m, recs)
          = {m} \cup DeepestKnownAssemble(recs)[Sig(m)][2].prevtran
    BY <1>a, <1>dk DEF PrevTranAssemble
  <2> QED BY <1>pt, <1>dk, <2>1, <2>ptz, <1>a
<1>b. CASE Sig(m) \notin DOMAIN DeepestKnown(m)
  <2>1. PrevTranAssemble(m, recs) = {m}  BY <1>b, <1>dk DEF PrevTranAssemble
  <2> QED BY <1>pt, <2>1, <1>b
<1> QED BY <1>a, <1>b
====================================================================
