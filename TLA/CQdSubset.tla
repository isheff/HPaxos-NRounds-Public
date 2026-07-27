------------------------------- MODULE CQdSubset -------------------------------
EXTENDS MessageConcrete, CCflRec, CTranLevelLE, CCflId

\* a CCfl record's own qd images stay inside its subject's CTranExcl
LEMMA CQdSubset ==
  ASSUME NEW z \in CMC, NEW alpha \in Learners, NEW dd \in Nat
  PROVE CCfl(z).qd[<<alpha, dd>>] \subseteq CTranExcl(z)
<1> SUFFICES ASSUME NEW ee \in CCfl(z).qd[<<alpha, dd>>] PROVE ee \in CTranExcl(z)
  OBVIOUS
<1>1. CCfl(z) = CCflR(z, {CCfl(p) : p \in CTranExcl(z)})  BY CCflRec
<1>2. CCfl(z).qd = CCflR(z, {CCfl(p) : p \in CTranExcl(z)}).qd  BY <1>1
<1>3. CCfl(z).qd = [pr \in Learners \X Nat |->
        LET al == pr[1]  dl == pr[2]
        IN {yy.id : yy \in {mm \in {CCfl(p) : p \in CTranExcl(z)} :
              /\ dl > 0
              /\ CB(mm.id) = CB(z)
              /\ CSig(mm.id) \in Acceptors
              /\ dl = 1 => (CIsOneB(mm.id) /\ mm.fresh[al])
              /\ dl > 1 => CSigS(mm.qd[<<al, dl-1>>]) \in Quorums(al)}}]
  BY <1>2 DEF CCflR
<1>4. CCfl(z).qd[<<alpha, dd>>] =
        {yy.id : yy \in {mm \in {CCfl(p) : p \in CTranExcl(z)} :
              /\ dd > 0
              /\ CB(mm.id) = CB(z)
              /\ CSig(mm.id) \in Acceptors
              /\ dd = 1 => (CIsOneB(mm.id) /\ mm.fresh[alpha])
              /\ dd > 1 => CSigS(mm.qd[<<alpha, dd-1>>]) \in Quorums(alpha)}}
  BY <1>3
<1>5. \A p \in CTranExcl(z) : CCfl(p).id = p
  <2> SUFFICES ASSUME NEW p \in CTranExcl(z) PROVE CCfl(p).id = p  OBVIOUS
  <2>1. p \in CTran(z)  BY DEF CTranExcl
  <2>2. p \in CMC  BY <2>1, CTranLevelLE DEF CTranBelowProp
  <2> QED BY <2>2, CCflId
<1>6. PICK yy \in {mm \in {CCfl(p) : p \in CTranExcl(z)} : TRUE} : ee = yy.id
  BY <1>4
<1>7. PICK p \in CTranExcl(z) : yy = CCfl(p)  BY <1>6
<1>8. ee = CCfl(p).id  BY <1>6, <1>7
<1>9. ee = p  BY <1>8, <1>5, <1>7
<1> QED BY <1>9, <1>7
=============================================================================
