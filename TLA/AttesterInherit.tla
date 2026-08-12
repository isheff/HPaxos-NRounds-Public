--------------------------- MODULE AttesterInherit ---------------------------
\*   HasDepthDef, QuorumUpward, TranSubMessages -> cited lemmas
\*   FiniteSetTheorems -> FS_Subset, FS_Image
\*   TLAPS -> SMT; proof-only
EXTENDS MessageInterface, HasDepthDef, QuorumUpward, TranSubMessages,
        FiniteSetTheorems
LOCAL INSTANCE TLAPS

\* An acceptor-signed message inherits any same-ballot ancestor's depth-d
\* attestation (d >= 1): the ancestor's level-(d-1) quorum sits inside the
\* descendant's Qd at the same level, and quorums are upward closed.
LEMMA AttesterInherit ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         NEW alpha \in Learners, NEW x \in Messages, Sig(x) \in Acceptors,
         NEW y \in TranExclusive(x), B(y) = B(x),
         NEW d \in Nat, d >= 1, HasDepth(alpha, y, d)
  PROVE HasDepth(alpha, x, d)
<1>yM. y \in Messages  BY TranSubMessages DEF TranExclusive
<1>hdy. SigS(Qd(alpha, y, d)) \in Quorums(alpha)
  <2>1. HasDepth(alpha, y, d) =
          (/\ Sig(y) \in Acceptors
           /\ IF d = 0 THEN (IsOneB(y) /\ Fresh(alpha, y))
                       ELSE SigS(Qd(alpha, y, d)) \in Quorums(alpha))
    BY <1>yM, HasDepthDef
  <2> QED BY <2>1, SMT
<1>sub. Qd(alpha, y, d) \subseteq Qd(alpha, x, d)
  <2> SUFFICES ASSUME NEW z \in Qd(alpha, y, d)
      PROVE z \in Qd(alpha, x, d)  OBVIOUS
  <2>1. z \in TranExclusive(y) /\ B(y) = B(z) /\ HasDepth(alpha, z, d - 1)
    BY DEF Qd
  <2>2. z \in Tran(x)
    <3>1. y \in Tran(x)  BY DEF TranExclusive
    <3>2. Tran(y) \subseteq Tran(x)  BY <3>1 DEF TranTrans
    <3> QED BY <2>1, <3>2 DEF TranExclusive
  <2>3. z # x
    <3>1. CASE z = x
      <4>1. x \in Tran(y)  BY <2>1, <3>1 DEF TranExclusive
      <4>2. x \notin Tran(y)  BY DEF TranAcyclic
      <4> QED BY <4>1, <4>2
    <3> QED BY <3>1
  <2>4. z \in TranExclusive(x)  BY <2>2, <2>3 DEF TranExclusive
  <2> QED BY <2>1, <2>4 DEF Qd
<1>acc. SigS(Qd(alpha, x, d)) \subseteq Acceptors
  <2> SUFFICES ASSUME NEW a \in SigS(Qd(alpha, x, d))
      PROVE a \in Acceptors  OBVIOUS
  <2>1. PICK z \in Qd(alpha, x, d) : a = Sig(z)  BY DEF SigS
  <2>2. HasDepth(alpha, z, d - 1)  BY <2>1 DEF Qd
  <2>3. z \in Messages
    <3>1. z \in TranExclusive(x)  BY <2>1 DEF Qd
    <3> QED BY <3>1, TranSubMessages DEF TranExclusive
  <2>4. d - 1 \in Nat  BY SMT
  <2>5. Sig(z) \in Acceptors
    <3>1. HasDepth(alpha, z, d - 1) =
            (/\ Sig(z) \in Acceptors
             /\ IF d - 1 = 0 THEN (IsOneB(z) /\ Fresh(alpha, z))
                             ELSE SigS(Qd(alpha, z, d - 1)) \in Quorums(alpha))
      BY <2>3, <2>4, HasDepthDef
    <3> QED BY <3>1, <2>2
  <2> QED BY <2>1, <2>5
<1>fin. IsFiniteSet(SigS(Qd(alpha, x, d)))
  <2>1. Qd(alpha, x, d) \subseteq Tran(x)  BY DEF Qd, TranExclusive
  <2>2. IsFiniteSet(Tran(x))  BY DEF TranFinite
  <2>3. IsFiniteSet(Qd(alpha, x, d))  BY <2>1, <2>2, FS_Subset
  <2> QED BY <2>3, FS_Image DEF SigS
<1>mono. SigS(Qd(alpha, y, d)) \subseteq SigS(Qd(alpha, x, d))
  BY <1>sub DEF SigS
<1>q. SigS(Qd(alpha, x, d)) \in Quorums(alpha)
  BY <1>hdy, <1>mono, <1>acc, <1>fin, QuorumUpward
<1> QED
  <2>1. HasDepth(alpha, x, d) =
          (/\ Sig(x) \in Acceptors
           /\ IF d = 0 THEN (IsOneB(x) /\ Fresh(alpha, x))
                       ELSE SigS(Qd(alpha, x, d)) \in Quorums(alpha))
    BY HasDepthDef
  <2> QED BY <2>1, <1>q, SMT
====================================================================
