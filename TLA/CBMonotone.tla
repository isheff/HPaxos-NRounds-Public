------------------------------ MODULE CBMonotone ------------------------------
EXTENDS MessageConcrete, CMessageTranClosed, CMessagesSubMC, CTranTrans,
        CFiniteTran, CSelfInTran, CMaxSubsetMonotone, FiniteSetTheorems

\* If y is in x's Tran-closure (with x already Message-good), y's ballot
\* never exceeds x's -- x's proposal-set contains everything y's does.
LEMMA CBMonotone ==
  ASSUME NEW x \in CMessages, NEW y \in CTran(x)
  PROVE CB(y) <= CB(x)
<1>1. y \in CMessages  BY CMessageTranClosed
<1>2. x \in CMC  BY CMessagesSubMC
<1>3. y \in CMC  BY <1>1, CMessagesSubMC
<1>4. CTran(y) \subseteq CTran(x)  BY <1>2, CTranTrans
<1> DEFINE Px == {w \in CTran(x) : CIsProposal(w)}
<1> DEFINE Py == {w \in CTran(y) : CIsProposal(w)}
<1>5. Py \subseteq Px  BY <1>4
<1>6. IsFiniteSet(CTran(x))  BY <1>2, CFiniteTran
<1>7. IsFiniteSet(Px)  BY <1>6, FS_Subset
<1>8. Px # {}
  <2>0. x \in CTran(x)  BY <1>2, CSelfInTran
  <2>wf. \A z \in CTran(x) : CWellFormed(z)  BY DEF CMessages
  <2>1. CWellFormed(x)  BY <2>0, <2>wf
  <2>2. \E a \in CTran(x) : CIsProposal(a)  BY <2>1 DEF CWellFormed
  <2> QED BY <2>2
<1>9. Py # {}
  <2>0. y \in CTran(y)  BY <1>3, CSelfInTran
  <2>wf. \A z \in CTran(y) : CWellFormed(z)  BY <1>1 DEF CMessages
  <2>1. CWellFormed(y)  BY <2>0, <2>wf
  <2>2. \E a \in CTran(y) : CIsProposal(a)  BY <2>1 DEF CWellFormed
  <2> QED BY <2>2
<1> DEFINE ImgX == {w.payload.ballot : w \in Px}
<1> DEFINE ImgY == {w.payload.ballot : w \in Py}
<1>10. ImgY \subseteq ImgX  BY <1>5
<1>11. \A z \in ImgX : z \in Nat
  <2> SUFFICES ASSUME NEW w \in Px PROVE w.payload.ballot \in Nat  OBVIOUS
  <2>1. w \in CTran(x) /\ CIsProposal(w)  OBVIOUS
  <2>2. w.payload \in CProposal  BY <2>1 DEF CIsProposal
  <2>3. PICK bb \in Ballots : w.payload = [type |-> "proposal", ballot |-> bb]  BY <2>2 DEF CProposal
  <2>4. w.payload.ballot = bb  BY <2>3
  <2>5. bb \in Nat  BY DEF Ballots
  <2> QED BY <2>4, <2>5
<1>12. IsFiniteSet(ImgX)  BY <1>7, FS_Image
<1>13. ImgY # {}  BY <1>9
<1>14. Max(ImgY) <= Max(ImgX)  BY <1>12, <1>10, <1>13, <1>11, CMaxSubsetMonotone
<1> QED BY <1>14 DEF CB
=============================================================================
