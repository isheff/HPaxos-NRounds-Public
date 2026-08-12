---------------------------- MODULE FreshResolve ----------------------------
\*   DigestRec, CaughtRec, BalRec, BBallot, TranSubMessages -> cited lemmas
\*   TLAPS -> SMT; proof-only
EXTENDS RecursiveWellFormed, DigestRec, CaughtStep, CaughtRec, BalStep,
        BalRec, BBallot, TranSubMessages
LOCAL INSTANCE TLAPS

\* Generalized step version of FreshRec: over ANY digest set S between
\* Refs(m) and TranExclusive(m), given the correctness of the highesttwoas
\* assembly over S as a HYPOTHESIS (so the combined induction can supply it
\* mid-step), the assembled fresh check decides Fresh exactly. See
\* FreshRec for the field-level corollary.
LEMMA FreshResolve ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         AlwaysAProposal,
         NEW m \in Messages,
         NEW S, Refs(m) \subseteq S, S \subseteq TranExclusive(m),
         HighestTwoAsCorrect(m, HighestTwoAsAssemble({Digest(p) : p \in S})),
         NEW alpha \in Learners
  PROVE FreshAssemble(alpha, m, {Digest(p) : p \in S}) <=> Fresh(alpha, m)
<1> DEFINE recs == {Digest(p) : p \in S}
<1> DEFINE ht == HighestTwoAsAssemble(recs)
<1> DEFINE CC == Con(alpha, m)
<1> DEFINE DD == DOMAIN HighestTwoAsAssemble(recs)
<1>SM. S \subseteq Messages  BY TranSubMessages DEF TranExclusive
<1>con. ConFromCaught(alpha, CaughtAssemble(recs)) = Con(alpha, m)
  <2>1. \A p \in S : DigestCaught(p) = Caught(p)  BY <1>SM, CaughtRec
  <2>2. CaughtAssemble(recs) = Caught(m)  BY <2>1, CaughtStep
  <2> QED BY <2>2 DEF Con
<1>bv. BalToVal(BalAssemble(m, recs)) = V(m)
  <2>1. \A p \in S : DigestBal(p) = B(p)  BY <1>SM, BalRec
  <2>2. BalAssemble(m, recs) = B(m)  BY <2>1, BalStep
  <2> QED BY <2>2 DEF V
<1>cond. FreshAssemble(alpha, m, recs) <=>
    (\A l \in CC \cap DD :
       \/ BalToVal(ht[l].bal) = V(m)
       \/ \E l2 \in CC \cap DD : ht[l2].bal > ht[l].bal)
  BY <1>con, <1>bv DEF FreshAssemble
<1>inv. HighestTwoAsCorrect(m, ht)  OBVIOUS
<1>dom. DD = {l \in Learners : \E y \in TranExclusive(m) : l \in Lrns(y)}
  BY <1>inv DEF HighestTwoAsCorrect
<1>tnat. \A y \in Tran(m) : B(y) \in Nat
  <2> SUFFICES ASSUME NEW y \in Tran(m) PROVE B(y) \in Nat  OBVIOUS
  <2>1. y \in Messages  BY TranSubMessages
  <2>2. B(y) \in Ballots  BY <2>1, BBallot
  <2> QED BY <2>2 DEF Ballots
<1>ents. \A l \in DD :
   /\ ht[l].id \in TranExclusive(m)
   /\ l \in Lrns(ht[l].id)
   /\ ht[l].bal = B(ht[l].id)
   /\ ht[l].bal \in Nat
   /\ \A y \in TranExclusive(m) : l \in Lrns(y) => B(y) <= B(ht[l].id)
  <2> SUFFICES ASSUME NEW l \in DD
      PROVE /\ ht[l].id \in TranExclusive(m)
            /\ l \in Lrns(ht[l].id)
            /\ ht[l].bal = B(ht[l].id)
            /\ ht[l].bal \in Nat
            /\ \A y \in TranExclusive(m) : l \in Lrns(y) => B(y) <= B(ht[l].id)
    OBVIOUS
  <2>1. /\ ht[l] = Digest(ht[l].id)
        /\ ht[l].id \in TranExclusive(m)
        /\ l \in Lrns(ht[l].id)
        /\ \A y \in TranExclusive(m) : l \in Lrns(y) => B(y) <= B(ht[l].id)
    BY <1>inv DEF HighestTwoAsCorrect
  <2>2. ht[l].id \in Messages  BY <2>1, TranSubMessages DEF TranExclusive
  <2>3. DigestBal(ht[l].id) = B(ht[l].id)  BY <2>2, BalRec
  <2>4. ht[l].bal = B(ht[l].id)  BY <2>1, <2>3 DEF DigestBal
  <2>5. B(ht[l].id) \in Ballots  BY <2>2, BBallot
  <2> QED BY <2>1, <2>4, <2>5 DEF Ballots
\* -------------------------------------------------------------- forward
<1>fwd. (\A l \in CC \cap DD :
           \/ BalToVal(ht[l].bal) = V(m)
           \/ \E l2 \in CC \cap DD : ht[l2].bal > ht[l].bal)
        => Fresh(alpha, m)
  <2>1. CASE \A l \in CC \cap DD :
               \/ BalToVal(ht[l].bal) = V(m)
               \/ \E l2 \in CC \cap DD : ht[l2].bal > ht[l].bal
    <3> SUFFICES ASSUME NEW y \in Tran(m)
        PROVE \/ V(y) = V(m)
              \/ Con(alpha, m) \cap Lrns(y) = {}
              \/ \E p \in TranExclusive(m) :
                   B(p) > B(y) /\ Con(alpha, m) \cap Lrns(p) # {}
      BY DEF Fresh
    <3>a. CASE y = m
      <4> QED BY <3>a
    <3>b. CASE y # m
      <4>yTE. y \in TranExclusive(m)  BY <3>b DEF TranExclusive
      <4>c1. CASE Con(alpha, m) \cap Lrns(y) = {}
        <5> QED BY <4>c1
      <4>c2. CASE Con(alpha, m) \cap Lrns(y) # {}
        <5>l. PICK l \in Con(alpha, m) \cap Lrns(y) : TRUE  BY <4>c2
        <5>lL. l \in Learners  BY <5>l DEF Lrns
        <5>lD. l \in DD  BY <5>lL, <4>yTE, <5>l, <1>dom
        <5>e. /\ ht[l].id \in TranExclusive(m)
              /\ l \in Lrns(ht[l].id)
              /\ ht[l].bal = B(ht[l].id)
              /\ ht[l].bal \in Nat
              /\ \A yy \in TranExclusive(m) :
                   l \in Lrns(yy) => B(yy) <= B(ht[l].id)
          BY <5>lD, <1>ents
        <5>by. B(y) <= B(ht[l].id)  BY <5>e, <4>yTE, <5>l
        <5>ynat. B(y) \in Nat  BY <1>tnat
        <5>cnd. \/ BalToVal(ht[l].bal) = V(m)
                \/ \E l2 \in CC \cap DD : ht[l2].bal > ht[l].bal
          BY <2>1, <5>l, <5>lD
        <5>x. CASE BalToVal(ht[l].bal) = V(m)
          <6>a. CASE B(y) = B(ht[l].id)
            <7>1. V(y) = V(m)  BY <6>a, <5>e, <5>x DEF V
            <7> QED BY <7>1
          <6>b. CASE B(y) # B(ht[l].id)
            <7>lt. B(ht[l].id) > B(y)
              BY <5>by, <6>b, <5>e, <5>ynat, SMT
            <7> QED BY <7>lt, <5>e, <5>l
          <6> QED BY <6>a, <6>b
        <5>y2. CASE \E l2 \in CC \cap DD : ht[l2].bal > ht[l].bal
          <6>l2. PICK l2 \in CC \cap DD : ht[l2].bal > ht[l].bal  BY <5>y2
          <6>e2. /\ ht[l2].id \in TranExclusive(m)
                 /\ l2 \in Lrns(ht[l2].id)
                 /\ ht[l2].bal = B(ht[l2].id)
                 /\ ht[l2].bal \in Nat
            BY <6>l2, <1>ents
          <6>gt. B(ht[l2].id) > B(y)
            BY <6>l2, <6>e2, <5>e, <5>by, <5>ynat, SMT
          <6>ok. Con(alpha, m) \cap Lrns(ht[l2].id) # {}
            BY <6>l2, <6>e2
          <6> QED BY <6>gt, <6>ok, <6>e2
        <5> QED BY <5>cnd, <5>x, <5>y2
      <4> QED BY <4>c1, <4>c2
    <3> QED BY <3>a, <3>b
  <2> QED BY <2>1
\* ------------------------------------------------------------ backward
<1>bwd. Fresh(alpha, m) =>
        (\A l \in CC \cap DD :
           \/ BalToVal(ht[l].bal) = V(m)
           \/ \E l2 \in CC \cap DD : ht[l2].bal > ht[l].bal)
  <2>1. CASE Fresh(alpha, m)
    <3> SUFFICES ASSUME NEW l \in CC \cap DD
        PROVE \/ BalToVal(ht[l].bal) = V(m)
              \/ \E l2 \in CC \cap DD : ht[l2].bal > ht[l].bal
      OBVIOUS
    <3>e. /\ ht[l].id \in TranExclusive(m)
          /\ l \in Lrns(ht[l].id)
          /\ ht[l].bal = B(ht[l].id)
          /\ ht[l].bal \in Nat
      BY <1>ents
    <3>yT. ht[l].id \in Tran(m)  BY <3>e DEF TranExclusive
    <3>fr. \/ V(ht[l].id) = V(m)
           \/ Con(alpha, m) \cap Lrns(ht[l].id) = {}
           \/ \E p \in TranExclusive(m) :
                B(p) > B(ht[l].id) /\ Con(alpha, m) \cap Lrns(p) # {}
      BY <2>1, <3>yT DEF Fresh
    <3>a. CASE V(ht[l].id) = V(m)
      <4>1. BalToVal(ht[l].bal) = V(m)  BY <3>a, <3>e DEF V
      <4> QED BY <4>1
    <3>b. CASE Con(alpha, m) \cap Lrns(ht[l].id) = {}
      <4>1. l \in Con(alpha, m) \cap Lrns(ht[l].id)  BY <3>e
      <4> QED BY <4>1, <3>b
    <3>c. CASE \E p \in TranExclusive(m) :
                 B(p) > B(ht[l].id) /\ Con(alpha, m) \cap Lrns(p) # {}
      <4>p. PICK p \in TranExclusive(m) :
              B(p) > B(ht[l].id) /\ Con(alpha, m) \cap Lrns(p) # {}
        BY <3>c
      <4>l2. PICK l2 \in Con(alpha, m) \cap Lrns(p) : TRUE  BY <4>p
      <4>l2L. l2 \in Learners  BY <4>l2 DEF Lrns
      <4>l2D. l2 \in DD  BY <4>l2L, <4>p, <4>l2, <1>dom
      <4>e2. /\ ht[l2].bal = B(ht[l2].id)
             /\ ht[l2].bal \in Nat
             /\ \A yy \in TranExclusive(m) :
                  l2 \in Lrns(yy) => B(yy) <= B(ht[l2].id)
        BY <4>l2D, <1>ents
      <4>hi2. B(p) <= B(ht[l2].id)  BY <4>e2, <4>p, <4>l2
      <4>pnat. B(p) \in Nat
        <5>1. p \in Tran(m)  BY <4>p DEF TranExclusive
        <5> QED BY <5>1, <1>tnat
      <4>gt. ht[l2].bal > ht[l].bal
        BY <4>hi2, <4>p, <4>e2, <3>e, <4>pnat, SMT
      <4> QED BY <4>gt, <4>l2, <4>l2D
    <3> QED BY <3>fr, <3>a, <3>b, <3>c
  <2> QED BY <2>1
<1> QED BY <1>cond, <1>fwd, <1>bwd
====================================================================
