------------------------------ MODULE QdDef ------------------------------
EXTENDS MessageInterface, CombinedFreshQdLrnsIdRec, TranSubMessages, CflId

\* Qd(alpha, m, d) is the set of strict ancestors of m of matching ballot at
\* depth d-1.  Unfold CombinedFreshQdLrnsId(m), read off the qd field at
\* <<alpha,d>>, identify each recursive result y with its id (CflId), and
\* observe the comprehension's d=1 / d>1 conditions are exactly
\* HasDepth(.,.,d-1).
LEMMA QdDef ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         NEW alpha \in Learners,
         NEW m \in Messages,
         NEW d \in Nat
  PROVE Qd(alpha, m, d) = CombinedFreshQdLrnsId(m).qd[<<alpha, d>>]
<1> DEFINE RR == {CombinedFreshQdLrnsId(p) : p \in TranExclusive(m)}
<1> DEFINE cond(mm) == /\ d > 0
                       /\ B(mm.id) = B(m)
                       /\ Sig(mm.id) \in Acceptors
                       /\ d = 1 => (IsOneB(mm.id) /\ mm.fresh[alpha])
                       /\ d > 1 => SigS(mm.qd[<<alpha, d-1>>]) \in Quorums(alpha)
<1>rec. CombinedFreshQdLrnsId(m) = CombinedFreshQdLrnsIdR(m, RR)  BY CombinedFreshQdLrnsIdRec
<1>dom. <<alpha, d>> \in Learners \X Nat  OBVIOUS
<1>raw. CombinedFreshQdLrnsId(m).qd[<<alpha, d>>] = {y.id : y \in {mm \in RR : cond(mm)}}
  BY <1>rec, <1>dom DEF CombinedFreshQdLrnsIdR
<1>2. {y.id : y \in {mm \in RR : cond(mm)}} \subseteq Qd(alpha, m, d)
  <2> SUFFICES ASSUME NEW z \in {y.id : y \in {mm \in RR : cond(mm)}} PROVE z \in Qd(alpha, m, d)  OBVIOUS
  <2>1. PICK y \in {mm \in RR : cond(mm)} : z = y.id  OBVIOUS
  <2>2. y \in RR /\ cond(y)  BY <2>1
  <2>3. PICK p \in TranExclusive(m) : y = CombinedFreshQdLrnsId(p)  BY <2>2
  <2>4. p \in Messages  BY <2>3, TranSubMessages DEF TranExclusive
  <2>5. y.id = p  BY <2>3, <2>4, CflId
  <2>6. z = p  BY <2>1, <2>5
  <2>9. /\ d > 0 /\ B(p) = B(m) /\ Sig(p) \in Acceptors
        /\ (d = 1 => (IsOneB(p) /\ CombinedFreshQdLrnsId(p).fresh[alpha]))
        /\ (d > 1 => SigS(CombinedFreshQdLrnsId(p).qd[<<alpha, d-1>>]) \in Quorums(alpha))
    BY <2>2, <2>3, <2>5
  <2>10. HasDepth(alpha, p, d-1)  BY <2>9 DEF HasDepth
  <2> QED BY <2>3, <2>6, <2>9, <2>10 DEF Qd
<1>3. Qd(alpha, m, d) \subseteq {y.id : y \in {mm \in RR : cond(mm)}}
  <2> SUFFICES ASSUME NEW z \in Qd(alpha, m, d) PROVE z \in {y.id : y \in {mm \in RR : cond(mm)}}  OBVIOUS
  <2>1. z \in TranExclusive(m) /\ d > 0 /\ B(m) = B(z) /\ HasDepth(alpha, z, d-1)  BY DEF Qd
  <2>2. z \in Messages  BY <2>1, TranSubMessages DEF TranExclusive
  <2> DEFINE y == CombinedFreshQdLrnsId(z)
  <2>3. y \in RR  BY <2>1
  <2>4. y.id = z  BY <2>2, CflId
  <2>7. /\ Sig(z) \in Acceptors
        /\ d = 1 => (IsOneB(z) /\ y.fresh[alpha])
        /\ d > 1 => SigS(y.qd[<<alpha, d-1>>]) \in Quorums(alpha)
    BY <2>1 DEF HasDepth
  <2>8. cond(y)  BY <2>1, <2>4, <2>7
  <2>9. y \in {mm \in RR : cond(mm)}  BY <2>3, <2>8
  <2> QED BY <2>9, <2>4
<1> QED BY <1>raw, <1>2, <1>3
====================================================================
