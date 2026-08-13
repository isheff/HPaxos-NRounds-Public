---------------------------- MODULE IsOneBMemo ----------------------------
\*   MemoRec, BalRec, NewBalRec, IsOneBRec, TranSubMessages -> cited
\*   TLAPS -> proof-only
EXTENDS RecursiveWellFormed, MemoRec, BalRec, NewBalRec, IsOneBRec,
        TranSubMessages
LOCAL INSTANCE TLAPS

\* The isoneb flag is exactly IsOneB, by matching IsOneBAssemble's
\* memo-level conditions with IsOneBRec's refs-local characterization.
LEMMA IsOneBMemo ==
  ASSUME MessageInterfaceAssumptions, NEW m \in Messages
  PROVE MemoIsOneB(m) <=> IsOneB(m)
<1>tok. TypeOKMessageInterface  BY DEF MessageInterfaceAssumptions
<1>tf. TranFinite  BY DEF MessageInterfaceAssumptions
<1>tt. TranTrans  BY DEF MessageInterfaceAssumptions
<1>ta. TranAcyclic  BY DEF MessageInterfaceAssumptions
<1>anp. AlwaysAProposal  BY DEF MessageInterfaceAssumptions
<1> DEFINE recs == {Memo(p) : p \in Refs(m)}
<1>unf. Memo(m) = MemoR(m, recs)
  BY <1>tok, <1>tt, <1>tf, <1>ta, MemoRec
<1>io. MemoIsOneB(m) <=> IsOneBAssemble(m, recs)
  BY <1>unf DEF MemoIsOneB, MemoR
<1>bal. BalAssemble(m, recs) = B(m)
  <2>1. BalAssemble(m, recs) = MemoBal(m)  BY <1>unf DEF MemoBal, MemoR
  <2> QED BY <2>1, <1>tok, <1>tt, <1>tf, <1>ta, <1>anp, BalRec
<1>rM. Refs(m) \subseteq Messages
  <2>1. Refs(m) \subseteq TranExclusive(m)  BY DEF Refs
  <2> QED BY <2>1, <1>tok, <1>tt, TranSubMessages DEF TranExclusive
<1>idp. \A p \in Refs(m) : Memo(p).id = p /\ Memo(p).bal = B(p)
  <2> SUFFICES ASSUME NEW p \in Refs(m)
      PROVE Memo(p).id = p /\ Memo(p).bal = B(p)  OBVIOUS
  <2>1. p \in Messages  BY <1>rM
  <2>2. Memo(p) = MemoR(p, {Memo(q) : q \in Refs(p)})
    BY <2>1, <1>tok, <1>tt, <1>tf, <1>ta, MemoRec
  <2>3. MemoBal(p) = B(p)
    BY <2>1, <1>tok, <1>tt, <1>tf, <1>ta, <1>anp, BalRec
  <2> QED BY <2>2, <2>3 DEF MemoR, MemoBal
<1>nbp. \A p \in Refs(m) :
          Memo(p).newbal <=> (\A y \in Refs(p) : B(y) < B(p))
  <2> SUFFICES ASSUME NEW p \in Refs(m)
      PROVE Memo(p).newbal <=> (\A y \in Refs(p) : B(y) < B(p))  OBVIOUS
  <2>1. p \in Messages  BY <1>rM
  <2>2. MemoNewBal(p) <=> (\A y \in Refs(p) : B(y) < B(p))
    BY <2>1, <1>tok, <1>tt, <1>tf, <1>ta, <1>anp, NewBalRec
  <2> QED BY <2>2 DEF MemoNewBal
<1>selfref. \A p \in Refs(m) : p \notin Refs(p)
  <2> SUFFICES ASSUME NEW p \in Refs(m), p \in Refs(p) PROVE FALSE  OBVIOUS
  <2>1. p \in TranExclusive(p)  BY DEF Refs
  <2> QED BY <2>1 DEF TranExclusive
<1>rec. IsOneB(m) <=>
    (/\ ~IsProposal(m)
     /\ \E p \in Refs(m) :
          /\ IsProposal(p)
          /\ B(p) = B(m)
          /\ \A y \in (Refs(m) \cup Refs(p)) \ {p} : B(y) < B(m))
  BY IsOneBRec
<1>fwd. IsOneBAssemble(m, recs) => IsOneB(m)
  <2>1. CASE IsOneBAssemble(m, recs)
    <3>rc. PICK rc \in recs :
             /\ IsProposal(rc.id)
             /\ rc.bal = BalAssemble(m, recs)
             /\ rc.newbal
             /\ \A rc2 \in recs : rc2 = rc \/ rc2.bal < BalAssemble(m, recs)
      BY <2>1 DEF IsOneBAssemble
    <3>p. PICK p \in Refs(m) : rc = Memo(p)  OBVIOUS
    <3>prop. IsProposal(p)  BY <3>rc, <3>p, <1>idp
    <3>pb. B(p) = B(m)  BY <3>rc, <3>p, <1>idp, <1>bal
    <3>pref. \A y \in Refs(p) : B(y) < B(p)  BY <3>rc, <3>p, <1>nbp
    <3>oth. \A q \in Refs(m) : q = p \/ B(q) < B(m)
      <4> SUFFICES ASSUME NEW q \in Refs(m), q # p PROVE B(q) < B(m)
        OBVIOUS
      <4>1. Memo(q) \in recs  OBVIOUS
      <4>2. Memo(q) # rc  BY <3>p, <1>idp
      <4>3. Memo(q).bal < BalAssemble(m, recs)  BY <3>rc, <4>1, <4>2
      <4> QED BY <4>3, <1>idp, <1>bal
    <3>all. \A y \in (Refs(m) \cup Refs(p)) \ {p} : B(y) < B(m)
      <4> SUFFICES ASSUME NEW y \in (Refs(m) \cup Refs(p)) \ {p}
          PROVE B(y) < B(m)  OBVIOUS
      <4>a. CASE y \in Refs(m)
        <5> QED BY <4>a, <3>oth
      <4>b. CASE y \in Refs(p)
        <5> QED BY <4>b, <3>pref, <3>pb
      <4> QED BY <4>a, <4>b
    <3>np. ~IsProposal(m)  BY <2>1 DEF IsOneBAssemble
    <3> QED BY <3>np, <3>prop, <3>pb, <3>all, <1>rec
  <2> QED BY <2>1
<1>bwd. IsOneB(m) => IsOneBAssemble(m, recs)
  <2>1. CASE IsOneB(m)
    <3>p. PICK p \in Refs(m) :
            /\ IsProposal(p)
            /\ B(p) = B(m)
            /\ \A y \in (Refs(m) \cup Refs(p)) \ {p} : B(y) < B(m)
      BY <2>1, <1>rec
    <3>np. ~IsProposal(m)  BY <2>1, <1>rec
    <3>rc. Memo(p) \in recs  OBVIOUS
    <3>c1. IsProposal(Memo(p).id)  BY <3>p, <1>idp
    <3>c2. Memo(p).bal = BalAssemble(m, recs)  BY <3>p, <1>idp, <1>bal
    <3>c3. Memo(p).newbal
      <4>1. \A y \in Refs(p) : B(y) < B(p)
        <5> SUFFICES ASSUME NEW y \in Refs(p) PROVE B(y) < B(p)  OBVIOUS
        <5>1. y # p  BY <1>selfref
        <5>2. y \in (Refs(m) \cup Refs(p)) \ {p}  BY <5>1
        <5> QED BY <5>2, <3>p
      <4> QED BY <4>1, <1>nbp
    <3>c4. \A rc2 \in recs : rc2 = Memo(p) \/ rc2.bal < BalAssemble(m, recs)
      <4> SUFFICES ASSUME NEW rc2 \in recs, rc2 # Memo(p)
          PROVE rc2.bal < BalAssemble(m, recs)  OBVIOUS
      <4>1. PICK q \in Refs(m) : rc2 = Memo(q)  OBVIOUS
      <4>2. q # p  BY <4>1
      <4>3. q \in (Refs(m) \cup Refs(p)) \ {p}  BY <4>2
      <4>4. B(q) < B(m)  BY <4>3, <3>p
      <4> QED BY <4>1, <4>4, <1>idp, <1>bal
    <3> QED BY <3>np, <3>rc, <3>c1, <3>c2, <3>c3, <3>c4 DEF IsOneBAssemble
  <2> QED BY <2>1
<1> QED BY <1>io, <1>fwd, <1>bwd
====================================================================
