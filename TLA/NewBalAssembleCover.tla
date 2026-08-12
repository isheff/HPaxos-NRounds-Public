------------------------ MODULE NewBalAssembleCover ------------------------
\*   BalStep, BalRec, TranExclusiveRefs, TranSubMessages, BMonotone,
\*   BBallot, DigestRec -> cited lemmas
\*   TLAPS -> SMT; proof-only
EXTENDS RecursiveWellFormed, BalStep, BalRec, TranExclusiveRefs,
        TranSubMessages, BMonotone, BBallot, DigestRec
LOCAL INSTANCE TLAPS

\* The newbal check over ANY digest set between Refs(x) and
\* TranExclusive(x) still decides "all refs strictly lower": extra members
\* sit under some ref, so B-monotonicity makes them lower whenever the
\* refs are.
LEMMA NewBalAssembleCover ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         AlwaysAProposal,
         NEW x \in Messages,
         NEW S, Refs(x) \subseteq S, S \subseteq TranExclusive(x)
  PROVE NewBalAssemble(x, {Digest(p) : p \in S})
          <=> (\A y \in Refs(x) : B(y) < B(x))
<1> DEFINE recs == {Digest(p) : p \in S}
<1>SM. S \subseteq Messages  BY TranSubMessages DEF TranExclusive
<1>ihb. \A p \in S : DigestBal(p) = B(p)  BY <1>SM, BalRec
<1>bal. BalAssemble(x, recs) = B(x)  BY <1>ihb, BalStep
<1>idp. \A p \in S : Digest(p).bal = B(p)  BY <1>ihb DEF DigestBal
<1>tnat. \A y \in Tran(x) : B(y) \in Nat
  <2> SUFFICES ASSUME NEW y \in Tran(x) PROVE B(y) \in Nat  OBVIOUS
  <2>1. y \in Messages  BY TranSubMessages
  <2>2. B(y) \in Ballots  BY <2>1, BBallot
  <2> QED BY <2>2 DEF Ballots
<1>fwd. NewBalAssemble(x, recs) => (\A y \in Refs(x) : B(y) < B(x))
  <2>1. CASE NewBalAssemble(x, recs)
    <3> SUFFICES ASSUME NEW y \in Refs(x) PROVE B(y) < B(x)  OBVIOUS
    <3>1. Digest(y) \in recs  OBVIOUS
    <3>2. Digest(y).bal < BalAssemble(x, recs)
      BY <2>1, <3>1 DEF NewBalAssemble
    <3> QED BY <3>2, <1>idp, <1>bal
  <2> QED BY <2>1
<1>bwd. (\A y \in Refs(x) : B(y) < B(x)) => NewBalAssemble(x, recs)
  <2>1. CASE \A y \in Refs(x) : B(y) < B(x)
    <3> SUFFICES ASSUME NEW rc \in recs
        PROVE rc.bal < BalAssemble(x, recs)
      BY DEF NewBalAssemble
    <3>1. PICK p \in S : rc = Digest(p)  OBVIOUS
    <3>2. p \in TranExclusive(x)  OBVIOUS
    <3>3. TranExclusive(x) = UNION {Tran(r) : r \in Refs(x)}
      BY TranExclusiveRefs
    <3>4. PICK r \in Refs(x) : p \in Tran(r)  BY <3>2, <3>3
    <3>5. r \in Messages
      <4>1. r \in TranExclusive(x)  BY DEF Refs
      <4> QED BY <4>1, TranSubMessages DEF TranExclusive
    <3>6. B(p) <= B(r)  BY <3>4, <3>5, BMonotone
    <3>7. B(r) < B(x)  BY <3>4, <2>1
    <3>8. B(p) \in Nat /\ B(r) \in Nat /\ B(x) \in Nat
      <4>1. p \in Tran(x) /\ r \in Tran(x) /\ x \in Tran(x)
        BY <3>2, <3>4, <3>5 DEF TranExclusive, Refs, Tran
      <4> QED BY <4>1, <1>tnat
    <3>9. B(p) < B(x)  BY <3>6, <3>7, <3>8, SMT
    <3> QED BY <3>1, <3>9, <1>idp, <1>bal
  <2> QED BY <2>1
<1> QED BY <1>fwd, <1>bwd
====================================================================
