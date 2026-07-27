------------------------ MODULE CUnionTranFiniteClosed ------------------------
EXTENDS MessageConcrete, CMessagesSubMC, CFiniteTran, CMessageTranClosed,
        CTranTrans, FiniteSetTheorems

\* The Tran-closure of a finite subset of CMessages is finite, stays inside
\* CMessages, and is itself Tran-closed -- everything CGenTranRefs needs.
LEMMA CUnionTranFiniteClosed ==
  ASSUME NEW m, IsFiniteSet(m), m \subseteq CMessages
  PROVE /\ IsFiniteSet(UNION {CTran(x) : x \in m})
        /\ UNION {CTran(x) : x \in m} \subseteq CMessages
        /\ \A z \in UNION {CTran(x) : x \in m} : CTran(z) \subseteq UNION {CTran(x) : x \in m}
<1> DEFINE U == UNION {CTran(x) : x \in m}
<1>mmc. m \subseteq CMC  BY CMessagesSubMC
<1>fin. IsFiniteSet(U)
  <2>1. \A x \in m : IsFiniteSet(CTran(x))  BY <1>mmc, CFiniteTran
  <2>2. IsFiniteSet({CTran(x) : x \in m})  BY FS_Image
  <2> QED BY <2>1, <2>2, FS_UNION
<1>sub. U \subseteq CMessages
  <2> SUFFICES ASSUME NEW z \in U PROVE z \in CMessages  OBVIOUS
  <2>1. PICK x \in m : z \in CTran(x)  OBVIOUS
  <2>2. CTran(x) \subseteq CMessages  BY CMessageTranClosed
  <2> QED BY <2>1, <2>2
<1>closed. \A z \in U : CTran(z) \subseteq U
  <2> SUFFICES ASSUME NEW z \in U PROVE CTran(z) \subseteq U  OBVIOUS
  <2>1. PICK x \in m : z \in CTran(x)  OBVIOUS
  <2>2. x \in CMC  BY <1>mmc
  <2>3. CTran(z) \subseteq CTran(x)  BY <2>2, <2>1, CTranTrans
  <2>4. CTran(x) \subseteq U  BY <2>1
  <2> QED BY <2>3, <2>4
<1> QED BY <1>fin, <1>sub, <1>closed
=============================================================================
