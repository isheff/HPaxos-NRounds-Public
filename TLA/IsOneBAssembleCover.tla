------------------------ MODULE IsOneBAssembleCover ------------------------
\*   BalStep, BalRec, NewBalRec, IsOneBRec, TranExclusiveRefs,
\*   TranSubMessages, BMonotone, BBallot, MemoRec -> cited lemmas
\*   TLAPS -> SMT; proof-only
EXTENDS RecursiveWellFormed, BalStep, BalRec, NewBalRec, IsOneBRec,
        TranExclusiveRefs, TranSubMessages, BMonotone, BBallot, MemoRec
LOCAL INSTANCE TLAPS

\* The isoneb check over ANY memo set between Refs(x) and
\* TranExclusive(x) still decides IsOneB(x). Key: the "all other members
\* strictly lower" clause FORCES the witness proposal to be maximal (a
\* non-ref witness sits under a ref of equal ballot, contradicting the
\* clause), so the witness is a ref and IsOneBRec applies; conversely the
\* extra members are all bounded by refs, hence strictly lower.
LEMMA IsOneBAssembleCover ==
  ASSUME MessageInterfaceAssumptions,
         NEW x \in Messages,
         NEW S, Refs(x) \subseteq S, S \subseteq TranExclusive(x)
  PROVE IsOneBAssemble(x, {Memo(p) : p \in S}) <=> IsOneB(x)
<1>tok. TypeOKMessageInterface  BY DEF MessageInterfaceAssumptions
<1>tf. TranFinite  BY DEF MessageInterfaceAssumptions
<1>tt. TranTrans  BY DEF MessageInterfaceAssumptions
<1>ta. TranAcyclic  BY DEF MessageInterfaceAssumptions
<1>anp. AlwaysAProposal  BY DEF MessageInterfaceAssumptions
<1> DEFINE recs == {Memo(p) : p \in S}
<1>SM. S \subseteq Messages
  BY <1>tok, <1>tt, TranSubMessages DEF TranExclusive
<1>ihb. \A p \in S : MemoBal(p) = B(p)
  BY <1>SM, <1>tok, <1>tt, <1>tf, <1>ta, <1>anp, BalRec
<1>bal. BalAssemble(x, recs) = B(x)
  BY <1>ihb, <1>tok, <1>tt, <1>tf, <1>ta, <1>anp, BalStep
<1>idp. \A p \in S : Memo(p).id = p /\ Memo(p).bal = B(p)
  <2> SUFFICES ASSUME NEW p \in S
      PROVE Memo(p).id = p /\ Memo(p).bal = B(p)  OBVIOUS
  <2>1. p \in Messages  BY <1>SM
  <2>2. Memo(p) = MemoR(p, {Memo(q) : q \in Refs(p)})
    BY <2>1, <1>tok, <1>tt, <1>tf, <1>ta, MemoRec
  <2> QED BY <2>2, <1>ihb DEF MemoR, MemoBal
<1>nbp. \A p \in S :
          Memo(p).newbal <=> (\A y \in Refs(p) : B(y) < B(p))
  <2> SUFFICES ASSUME NEW p \in S
      PROVE Memo(p).newbal <=> (\A y \in Refs(p) : B(y) < B(p))  OBVIOUS
  <2>1. p \in Messages  BY <1>SM
  <2>2. MemoNewBal(p) <=> (\A y \in Refs(p) : B(y) < B(p))
    BY <2>1, <1>tok, <1>tt, <1>tf, <1>ta, <1>anp, NewBalRec
  <2> QED BY <2>2 DEF MemoNewBal
<1>tex. TranExclusive(x) = UNION {Tran(r) : r \in Refs(x)}
  BY <1>tok, <1>tf, <1>tt, <1>ta, TranExclusiveRefs
<1>refsM. Refs(x) \subseteq Messages
  <2>1. Refs(x) \subseteq TranExclusive(x)  BY DEF Refs
  <2> QED BY <2>1, <1>tok, <1>tt, TranSubMessages DEF TranExclusive
<1>tnat. \A y \in Tran(x) : B(y) \in Nat
  <2> SUFFICES ASSUME NEW y \in Tran(x) PROVE B(y) \in Nat  OBVIOUS
  <2>1. y \in Messages  BY <1>tok, <1>tt, TranSubMessages
  <2>2. B(y) \in Ballots  BY <2>1, <1>tok, <1>tf, <1>anp, BBallot
  <2> QED BY <2>2 DEF Ballots
<1>lower. \A q \in S : q # x /\ q \in Tran(x)
  <2> SUFFICES ASSUME NEW q \in S PROVE q # x /\ q \in Tran(x)  OBVIOUS
  <2>1. q \in TranExclusive(x)  OBVIOUS
  <2> QED BY <2>1 DEF TranExclusive
<1>rec. IsOneB(x) <=>
    (/\ ~IsProposal(x)
     /\ \E p \in Refs(x) :
          /\ IsProposal(p)
          /\ B(p) = B(x)
          /\ \A y \in (Refs(x) \cup Refs(p)) \ {p} : B(y) < B(x))
  BY IsOneBRec
<1>selfref. \A p \in Messages : p \notin Refs(p)
  <2> SUFFICES ASSUME NEW p \in Messages, p \in Refs(p) PROVE FALSE  OBVIOUS
  <2>1. p \in TranExclusive(p)  BY DEF Refs
  <2> QED BY <2>1 DEF TranExclusive
<1>fwd. IsOneBAssemble(x, recs) => IsOneB(x)
  <2>1. CASE IsOneBAssemble(x, recs)
    <3>rc. PICK rc \in recs :
             /\ IsProposal(rc.id)
             /\ rc.bal = BalAssemble(x, recs)
             /\ rc.newbal
             /\ \A rc2 \in recs : rc2 = rc \/ rc2.bal < BalAssemble(x, recs)
      BY <2>1 DEF IsOneBAssemble
    <3>p. PICK p \in S : rc = Memo(p)  OBVIOUS
    <3>prop. IsProposal(p)  BY <3>rc, <3>p, <1>idp
    <3>pb. B(p) = B(x)  BY <3>rc, <3>p, <1>idp, <1>bal
    <3>pref. \A y \in Refs(p) : B(y) < B(p)  BY <3>rc, <3>p, <1>nbp
    <3>oth. \A q \in S : q = p \/ B(q) < B(x)
      <4> SUFFICES ASSUME NEW q \in S, q # p PROVE B(q) < B(x)
        OBVIOUS
      <4>1. Memo(q) \in recs  OBVIOUS
      <4>2. Memo(q) # rc  BY <3>p, <1>idp
      <4>3. Memo(q).bal < BalAssemble(x, recs)  BY <3>rc, <4>1, <4>2
      <4> QED BY <4>3, <1>idp, <1>bal
    <3>pRefs. p \in Refs(x)
      <4>1. p \in TranExclusive(x)  OBVIOUS
      <4>2. PICK r \in Refs(x) : p \in Tran(r)  BY <4>1, <1>tex
      <4>a. CASE p = r
        <5> QED BY <4>a, <4>2
      <4>b. CASE p # r
        <5>1. r \in S  OBVIOUS
        <5>2. B(r) < B(x)  BY <5>1, <4>b, <3>oth
        <5>3. r \in Messages  BY <1>refsM
        <5>4. B(p) <= B(r)
          BY <4>2, <5>3, <1>tok, <1>tt, <1>tf, <1>anp, BMonotone
        <5>5. B(p) \in Nat /\ B(r) \in Nat /\ B(x) \in Nat
          <6>1. p \in Tran(x) /\ r \in Tran(x) /\ x \in Tran(x)
            BY <4>1, <5>1, <1>lower DEF Tran
          <6> QED BY <6>1, <1>tnat
        <5> QED BY <5>2, <5>4, <5>5, <3>pb, SMT
      <4> QED BY <4>a, <4>b
    <3>all. \A y \in (Refs(x) \cup Refs(p)) \ {p} : B(y) < B(x)
      <4> SUFFICES ASSUME NEW y \in (Refs(x) \cup Refs(p)) \ {p}
          PROVE B(y) < B(x)  OBVIOUS
      <4>a. CASE y \in Refs(x)
        <5>1. y \in S  BY <4>a
        <5> QED BY <4>a, <5>1, <3>oth
      <4>b. CASE y \in Refs(p)
        <5> QED BY <4>b, <3>pref, <3>pb
      <4> QED BY <4>a, <4>b
    <3>np. ~IsProposal(x)  BY <2>1 DEF IsOneBAssemble
    <3> QED BY <3>np, <3>prop, <3>pb, <3>pRefs, <3>all, <1>rec
  <2> QED BY <2>1
<1>bwd. IsOneB(x) => IsOneBAssemble(x, recs)
  <2>1. CASE IsOneB(x)
    <3>p. PICK p \in Refs(x) :
            /\ IsProposal(p)
            /\ B(p) = B(x)
            /\ \A y \in (Refs(x) \cup Refs(p)) \ {p} : B(y) < B(x)
      BY <2>1, <1>rec
    <3>np. ~IsProposal(x)  BY <2>1, <1>rec
    <3>pS. p \in S  OBVIOUS
    <3>pM. p \in Messages  BY <1>refsM
    <3>rc. Memo(p) \in recs  BY <3>pS
    <3>c1. IsProposal(Memo(p).id)  BY <3>p, <3>pS, <1>idp
    <3>c2. Memo(p).bal = BalAssemble(x, recs)
      BY <3>p, <3>pS, <1>idp, <1>bal
    <3>c3. Memo(p).newbal
      <4>1. \A y \in Refs(p) : B(y) < B(p)
        <5> SUFFICES ASSUME NEW y \in Refs(p) PROVE B(y) < B(p)  OBVIOUS
        <5>1. y # p  BY <3>pM, <1>selfref
        <5>2. y \in (Refs(x) \cup Refs(p)) \ {p}  BY <5>1
        <5> QED BY <5>2, <3>p
      <4> QED BY <4>1, <3>pS, <1>nbp
    <3>texp. TranExclusive(p) = UNION {Tran(r) : r \in Refs(p)}
      BY <3>pM, <1>tok, <1>tf, <1>tt, <1>ta, TranExclusiveRefs
    <3>c4. \A rc2 \in recs : rc2 = Memo(p) \/ rc2.bal < BalAssemble(x, recs)
      <4> SUFFICES ASSUME NEW rc2 \in recs, rc2 # Memo(p)
          PROVE rc2.bal < BalAssemble(x, recs)  OBVIOUS
      <4>q. PICK q \in S : rc2 = Memo(q)  OBVIOUS
      <4>qp. q # p  BY <4>q, <3>pS, <1>idp
      <4>qb. B(q) < B(x)
        <5>1. q \in TranExclusive(x)  OBVIOUS
        <5>r. PICK r \in Refs(x) : q \in Tran(r)  BY <5>1, <1>tex
        <5>rM. r \in Messages  BY <1>refsM
        <5>qM. q \in Messages  BY <1>SM
        <5>nat. B(q) \in Nat /\ B(r) \in Nat /\ B(x) \in Nat /\ B(p) \in Nat
          <6>1. q \in Tran(x) /\ r \in Tran(x) /\ x \in Tran(x) /\ p \in Tran(x)
            BY <5>1, <3>pS, <1>lower DEF Tran, Refs, TranExclusive
          <6> QED BY <6>1, <1>tnat
        <5>a. CASE q = r
          <6>1. q \in (Refs(x) \cup Refs(p)) \ {p}  BY <5>a, <5>r, <4>qp
          <6> QED BY <6>1, <3>p
        <5>b. CASE q # r
          <6>le. B(q) <= B(r)
            BY <5>r, <5>rM, <1>tok, <1>tt, <1>tf, <1>anp, BMonotone
          <6>a. CASE r = p
            <7>1. q \in TranExclusive(p)  BY <5>r, <5>b, <6>a DEF TranExclusive
            <7>2. PICK y \in Refs(p) : q \in Tran(y)  BY <7>1, <3>texp
            <7>3. y # p  BY <3>pM, <1>selfref
            <7>4. y \in (Refs(x) \cup Refs(p)) \ {p}  BY <7>2, <7>3
            <7>5. B(y) < B(x)  BY <7>4, <3>p
            <7>6. y \in Messages
              <8>1. y \in TranExclusive(p)  BY <7>2 DEF Refs
              <8> QED BY <8>1, <3>pM, <1>tok, <1>tt, TranSubMessages
                DEF TranExclusive
            <7>7. B(q) <= B(y)
              BY <7>2, <7>6, <1>tok, <1>tt, <1>tf, <1>anp, BMonotone
            <7>8. B(y) \in Nat
              <8>1. y \in TranExclusive(x)
                <9>1. y \in Tran(p)  BY <7>2 DEF Refs, TranExclusive
                <9> QED BY <9>1, <3>pS, <1>tex
              <8>2. y \in Tran(x)  BY <8>1 DEF TranExclusive
              <8> QED BY <8>2, <1>tnat
            <7> QED BY <7>5, <7>7, <7>8, <5>nat, SMT
          <6>b. CASE r # p
            <7>1. r \in (Refs(x) \cup Refs(p)) \ {p}  BY <5>r, <6>b
            <7>2. B(r) < B(x)  BY <7>1, <3>p
            <7> QED BY <6>le, <7>2, <5>nat, SMT
          <6> QED BY <6>a, <6>b
        <5> QED BY <5>a, <5>b
      <4> QED BY <4>q, <4>qb, <1>idp, <1>bal
    <3> QED BY <3>np, <3>rc, <3>c1, <3>c2, <3>c3, <3>c4 DEF IsOneBAssemble
  <2> QED BY <2>1
<1> QED BY <1>fwd, <1>bwd
====================================================================
