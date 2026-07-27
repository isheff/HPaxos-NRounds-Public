------------------------------ MODULE CQdCompute ------------------------------
EXTENDS MessageConcrete, CCflRec, CTranLevelLE, CCflId

\* Concrete analogue of QdDef: computes a message's qd field at depth dd >= 1
\* as the set of its strict ancestors of matching ballot with depth dd-1.
LEMMA CQdCompute ==
  ASSUME NEW z \in CMC, NEW alpha \in Learners, NEW dd \in Nat, dd >= 1
  PROVE CCfl(z).qd[<<alpha, dd>>]
        = {p \in CTranExcl(z) : CB(p) = CB(z) /\ CHasDepth(alpha, p, dd-1)}
<1> DEFINE RR == {CCfl(p) : p \in CTranExcl(z)}
<1> DEFINE cond(mm) == /\ dd > 0
                       /\ CB(mm.id) = CB(z)
                       /\ CSig(mm.id) \in Acceptors
                       /\ dd = 1 => (CIsOneB(mm.id) /\ mm.fresh[alpha])
                       /\ dd > 1 => CSigS(mm.qd[<<alpha, dd-1>>]) \in Quorums(alpha)
<1>rec. CCfl(z) = CCflR(z, RR)  BY CCflRec
<1>dom. <<alpha, dd>> \in Learners \X Nat  OBVIOUS
<1>raw. CCfl(z).qd[<<alpha, dd>>] = {yy.id : yy \in {mm \in RR : cond(mm)}}
  BY <1>rec, <1>dom DEF CCflR
<1>id. \A p \in CTranExcl(z) : CCfl(p).id = p
  <2> SUFFICES ASSUME NEW p \in CTranExcl(z) PROVE CCfl(p).id = p  OBVIOUS
  <2>1. p \in CTran(z)  BY DEF CTranExcl
  <2>2. p \in CMC  BY <2>1, CTranLevelLE DEF CTranBelowProp
  <2> QED BY <2>2, CCflId
<1>cc. \A p \in CTranExcl(z) : cond(CCfl(p)) <=> (CB(p) = CB(z) /\ CHasDepth(alpha, p, dd-1))
  <2> SUFFICES ASSUME NEW p \in CTranExcl(z)
               PROVE cond(CCfl(p)) <=> (CB(p) = CB(z) /\ CHasDepth(alpha, p, dd-1))
    OBVIOUS
  <2>pid. CCfl(p).id = p  BY <1>id
  <2>hd. CHasDepth(alpha, p, dd-1) =
           (CSig(p) \in Acceptors /\
            IF dd-1 = 0 THEN (CIsOneB(p) /\ CCfl(p).fresh[alpha])
                        ELSE CSigS(CCfl(p).qd[<<alpha, dd-1>>]) \in Quorums(alpha))
    BY DEF CHasDepth
  <2>1. CASE dd = 1
    <3>a. cond(CCfl(p)) <=> (CB(p) = CB(z) /\ CSig(p) \in Acceptors /\ CIsOneB(p) /\ CCfl(p).fresh[alpha])
      BY <2>pid, <2>1
    <3>b. CHasDepth(alpha, p, dd-1) = (CSig(p) \in Acceptors /\ CIsOneB(p) /\ CCfl(p).fresh[alpha])
      BY <2>hd, <2>1
    <3> QED BY <3>a, <3>b
  <2>2. CASE dd > 1
    <3>a. cond(CCfl(p)) <=> (CB(p) = CB(z) /\ CSig(p) \in Acceptors
                             /\ CSigS(CCfl(p).qd[<<alpha, dd-1>>]) \in Quorums(alpha))
      BY <2>pid, <2>2
    <3>b. CHasDepth(alpha, p, dd-1) = (CSig(p) \in Acceptors
                             /\ CSigS(CCfl(p).qd[<<alpha, dd-1>>]) \in Quorums(alpha))
      <4>1. dd - 1 # 0  BY <2>2
      <4> QED BY <2>hd, <4>1
    <3> QED BY <3>a, <3>b
  <2> QED BY <2>1, <2>2
<1>sub. CCfl(z).qd[<<alpha, dd>>] \subseteq {p \in CTranExcl(z) : CB(p) = CB(z) /\ CHasDepth(alpha, p, dd-1)}
  <2> SUFFICES ASSUME NEW ee \in CCfl(z).qd[<<alpha, dd>>]
               PROVE ee \in {p \in CTranExcl(z) : CB(p) = CB(z) /\ CHasDepth(alpha, p, dd-1)}
    OBVIOUS
  <2>1. PICK yy \in {mm \in RR : cond(mm)} : ee = yy.id  BY <1>raw
  <2>2. yy \in RR /\ cond(yy)  BY <2>1
  <2>3. PICK p \in CTranExcl(z) : yy = CCfl(p)  BY <2>2
  <2>4. ee = p  BY <2>1, <2>3, <1>id
  <2>5. cond(CCfl(p))  BY <2>2, <2>3
  <2>6. CB(p) = CB(z) /\ CHasDepth(alpha, p, dd-1)  BY <2>5, <1>cc
  <2> QED BY <2>3, <2>4, <2>6
<1>sup. {p \in CTranExcl(z) : CB(p) = CB(z) /\ CHasDepth(alpha, p, dd-1)} \subseteq CCfl(z).qd[<<alpha, dd>>]
  <2> SUFFICES ASSUME NEW p \in CTranExcl(z), CB(p) = CB(z), CHasDepth(alpha, p, dd-1)
               PROVE p \in CCfl(z).qd[<<alpha, dd>>]
    OBVIOUS
  <2>1. CCfl(p) \in RR  OBVIOUS
  <2>2. cond(CCfl(p))  BY <1>cc
  <2>3. CCfl(p) \in {mm \in RR : cond(mm)}  BY <2>1, <2>2
  <2>4. CCfl(p).id = p  BY <1>id
  <2> QED BY <2>3, <2>4, <1>raw
<1> QED BY <1>sub, <1>sup
=============================================================================
