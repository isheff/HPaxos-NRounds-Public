------------------------------- MODULE CBTypeNat -------------------------------
EXTENDS MessageConcrete, CMessagesSubMC, CSelfInTran, CFiniteTran,
        MaxProps, FiniteSetTheorems

LEMMA CBTypeNat ==
  ASSUME NEW x \in CMessages
  PROVE CB(x) \in Nat
<1>0. x \in CTran(x)  BY CMessagesSubMC, CSelfInTran
<1>wf. \A zz \in CTran(x) : CWellFormed(zz)  BY DEF CMessages
<1>1. CWellFormed(x)  BY <1>0, <1>wf
<1>2. \E a \in CTran(x) : CIsProposal(a)  BY <1>1 DEF CWellFormed
<1> DEFINE Px == {w \in CTran(x) : CIsProposal(w)}
<1>3. Px # {}  BY <1>2
<1>4. IsFiniteSet(CTran(x))  BY CMessagesSubMC, CFiniteTran
<1>5. IsFiniteSet(Px)  BY <1>4, FS_Subset
<1> DEFINE ImgX == {w.payload.ballot : w \in Px}
<1>6. \A z \in ImgX : z \in Nat
  <2> SUFFICES ASSUME NEW w \in Px PROVE w.payload.ballot \in Nat  OBVIOUS
  <2>1. w.payload \in CProposal  BY DEF CIsProposal
  <2>2. PICK bb \in Ballots : w.payload = [type |-> "proposal", ballot |-> bb]  BY <2>1 DEF CProposal
  <2>3. w.payload.ballot = bb  BY <2>2
  <2>4. bb \in Nat  BY DEF Ballots
  <2> QED BY <2>3, <2>4
<1>7. IsFiniteSet(ImgX)  BY <1>5, FS_Image
<1>8. ImgX # {}  BY <1>3
<1>9. Max(ImgX) \in ImgX  BY <1>7, <1>8, <1>6, MaxProps
<1> QED BY <1>9, <1>6 DEF CB
=============================================================================
