----------------------------- MODULE NewBalRec -----------------------------
\*   DigestRec, BalRec, TranSubMessages -> cited lemmas
\*   TLAPS -> proof-only
EXTENDS RecursiveWellFormed, DigestRec, BalRec, TranSubMessages
LOCAL INSTANCE TLAPS

\* The newbal flag is exactly "all refs strictly lower-ballot".
LEMMA NewBalRec ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         AlwaysAProposal,
         NEW m \in Messages
  PROVE DigestNewBal(m) <=> (\A y \in Refs(m) : B(y) < B(m))
<1> DEFINE recs == {Digest(p) : p \in Refs(m)}
<1>unf. Digest(m) = DigestR(m, recs)  BY DigestRec
<1>nb. DigestNewBal(m) <=> NewBalAssemble(m, recs)
  BY <1>unf DEF DigestNewBal, DigestR
<1>bal. BalAssemble(m, recs) = B(m)
  <2>1. BalAssemble(m, recs) = DigestBal(m)  BY <1>unf DEF DigestBal, DigestR
  <2> QED BY <2>1, BalRec
<1>rM. Refs(m) \subseteq Messages
  <2>1. Refs(m) \subseteq TranExclusive(m)  BY DEF Refs
  <2> QED BY <2>1, TranSubMessages DEF TranExclusive
<1>idp. \A p \in Refs(m) : Digest(p).bal = B(p)
  <2> SUFFICES ASSUME NEW p \in Refs(m) PROVE Digest(p).bal = B(p)  OBVIOUS
  <2>1. p \in Messages  BY <1>rM
  <2>2. DigestBal(p) = B(p)  BY <2>1, BalRec
  <2> QED BY <2>2 DEF DigestBal
<1>fwd. NewBalAssemble(m, recs) => (\A y \in Refs(m) : B(y) < B(m))
  <2>1. CASE NewBalAssemble(m, recs)
    <3> SUFFICES ASSUME NEW y \in Refs(m) PROVE B(y) < B(m)  OBVIOUS
    <3>1. Digest(y) \in recs  OBVIOUS
    <3>2. Digest(y).bal < BalAssemble(m, recs)
      BY <2>1, <3>1 DEF NewBalAssemble
    <3> QED BY <3>2, <1>idp, <1>bal
  <2> QED BY <2>1
<1>bwd. (\A y \in Refs(m) : B(y) < B(m)) => NewBalAssemble(m, recs)
  <2>1. CASE \A y \in Refs(m) : B(y) < B(m)
    <3> SUFFICES ASSUME NEW rc \in recs
        PROVE rc.bal < BalAssemble(m, recs)
      BY DEF NewBalAssemble
    <3>1. PICK p \in Refs(m) : rc = Digest(p)  OBVIOUS
    <3> QED BY <3>1, <2>1, <1>idp, <1>bal
  <2> QED BY <2>1
<1> QED BY <1>nb, <1>fwd, <1>bwd
====================================================================
