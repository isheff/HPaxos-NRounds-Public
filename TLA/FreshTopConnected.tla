------------------------- MODULE FreshTopConnected -------------------------
EXTENDS MessageInterface, FiniteSetTheorems,
        TranSubMessages, BBallot, BMaxExists

\* The engine of the chain step (paper Definition 17 used at the top
\* ballot): if a fresh message r references a value-disagreeing message w
\* that carries a connected learner, then r references a strictly
\* higher-ballot message p that ALSO carries a connected learner and agrees
\* with r's value.
LEMMA FreshTopConnected ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         AlwaysAProposal,
         NEW gamma \in Learners, NEW r \in Messages,
         Fresh(gamma, r),
         NEW w \in Tran(r),
         V(w) # V(r),
         Con(gamma, r) \cap Lrns(w) # {}
  PROVE \E p \in Tran(r) :
          /\ B(p) > B(w)
          /\ V(p) = V(r)
          /\ Con(gamma, r) \cap Lrns(p) # {}
<1> DEFINE CandSet == {z \in Tran(r) : Con(gamma, r) \cap Lrns(z) # {}}
<1>wCand. w \in CandSet  OBVIOUS
<1>ne. CandSet # {}  BY <1>wCand
<1>finTr. IsFiniteSet(Tran(r))  BY DEF TranFinite
<1>fin. IsFiniteSet(CandSet)  BY <1>finTr, FS_Subset
<1>candM. CandSet \subseteq Messages
  <2> SUFFICES ASSUME NEW z \in CandSet PROVE z \in Messages  OBVIOUS
  <2>0. z \in Tran(r)  OBVIOUS
  <2> QED BY <2>0, TranSubMessages
<1>Bnat. \A z \in CandSet : B(z) \in Nat
  <2> SUFFICES ASSUME NEW z \in CandSet PROVE B(z) \in Nat  OBVIOUS
  <2>1. z \in Messages  BY <1>candM
  <2>2. B(z) \in Ballots  BY <2>1, BBallot
  <2> QED BY <2>2 DEF Ballots
<1>max. \E pp \in CandSet : \A y \in CandSet : B(y) <= B(pp)
  BY <1>fin, <1>ne, <1>candM, BMaxExists
<1> PICK p \in CandSet : \A y \in CandSet : B(y) <= B(p)  BY <1>max
<1>pR. p \in Tran(r)  OBVIOUS
<1>pCon. Con(gamma, r) \cap Lrns(p) # {}  OBVIOUS
<1>pMax. \A y \in CandSet : B(y) <= B(p)  OBVIOUS
\* p cannot be improved: applying Fresh at p rules out disjuncts 2 and 3
<1>notThird. \A pp \in TranExclusive(r) : ~(B(pp) > B(p) /\ Con(gamma, r) \cap Lrns(pp) # {})
  <2> SUFFICES ASSUME NEW pp \in TranExclusive(r), B(pp) > B(p), Con(gamma,r) \cap Lrns(pp) # {}
               PROVE FALSE
    OBVIOUS
  <2>1. pp \in Tran(r)  BY DEF TranExclusive
  <2>2. pp \in CandSet  BY <2>1
  <2>3. B(pp) <= B(p)  BY <2>2, <1>pMax
  <2>ty. B(pp) \in Nat /\ B(p) \in Nat  BY <1>Bnat, <2>2
  <2> QED BY <2>3, <2>ty
<1>freshP. \/ V(p) = V(r) \/ Con(gamma,r) \cap Lrns(p) = {}
           \/ \E pp \in TranExclusive(r): B(pp) > B(p) /\ Con(gamma,r) \cap Lrns(pp) # {}
  BY <1>pR DEF Fresh
<1>Veq. V(p) = V(r)  BY <1>freshP, <1>pCon, <1>notThird
\* separately: Fresh applied at w forces a strictly-higher candidate, so
\* p (the max) strictly beats w
<1>freshW. \/ V(w) = V(r) \/ Con(gamma,r) \cap Lrns(w) = {}
           \/ \E pp \in TranExclusive(r): B(pp) > B(w) /\ Con(gamma,r) \cap Lrns(pp) # {}
  BY DEF Fresh
<1>witPw. \E pp \in TranExclusive(r): B(pp) > B(w) /\ Con(gamma,r) \cap Lrns(pp) # {}
  BY <1>freshW
<1> PICK pw \in TranExclusive(r) : B(pw) > B(w) /\ Con(gamma,r) \cap Lrns(pw) # {}  BY <1>witPw
<1>pwR. pw \in Tran(r)  BY DEF TranExclusive
<1>pwCand. pw \in CandSet  BY <1>pwR
<1>pwLe. B(pw) <= B(p)  BY <1>pwCand, <1>pMax
<1>strict. B(p) > B(w)
  <2>ty. B(p) \in Nat /\ B(pw) \in Nat /\ B(w) \in Nat  BY <1>Bnat, <1>wCand, <1>pwCand
  <2> QED BY <1>pwLe, <2>ty
<1> QED BY <1>pR, <1>strict, <1>Veq, <1>pCon
====================================================================
