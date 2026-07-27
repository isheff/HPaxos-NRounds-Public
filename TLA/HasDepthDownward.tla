------------------------- MODULE HasDepthDownward -------------------------
\*   FiniteSetTheorems -> FS_Subset, FS_Image, GeneralNatInduction
\*   HasDepthDef, QuorumsHaveMembers, TranSubMessages, TranAntisym,
\*   QuorumUpward      -> cited lemmas
\*   TLAPS             -> IsaM; proof-only
EXTENDS MessageInterface, FiniteSetTheorems,
        HasDepthDef, QuorumsHaveMembers, TranSubMessages,
        TranAntisym, QuorumUpward
LOCAL INSTANCE TLAPS

\* Depth is downward closed above 1: a depth-d quorum's members supply the
\* depth-e quorums for every 1 <= e <= d, since Qd sets nest (via TranTrans)
\* and Quorums are upward closed.  (Does NOT extend to e = 0.)
LEMMA HasDepthDownward ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         LearnersMightAgree, ValidLearnerGraphAssumption,
         NEW alpha \in Learners, NEW x \in Messages,
         NEW d \in Nat, NEW e \in Nat,
         1 <= e, e <= d,
         HasDepth(alpha, x, d)
  PROVE HasDepth(alpha, x, e)
<1> DEFINE W(n) == {p \in TranExclusive(x) : B(p) = B(x) /\ HasDepth(alpha, p, n)}
<1> DEFINE Q(n) == SigS(W(n)) \in Quorums(alpha) => \A i \in 0..n : SigS(W(i)) \in Quorums(alpha)
<1>xSig. Sig(x) \in Acceptors  BY DEF HasDepth
<1>dpos. d >= 1  OBVIOUS
<1>epos. e >= 1  OBVIOUS
<1>dnat. d - 1 \in Nat  BY <1>dpos
<1>enat. e - 1 \in Nat  BY <1>epos
<1>drange. e - 1 \in 0..(d-1)  BY <1>dpos, <1>epos
<1>Wd1eq. W(d-1) = Qd(alpha, x, d)  BY <1>dpos DEF Qd
<1>We1eq. W(e-1) = Qd(alpha, x, e)  BY <1>epos DEF Qd
<1>hdd. Sig(x) \in Acceptors /\ SigS(Qd(alpha, x, d)) \in Quorums(alpha)
  <2>1. d # 0  BY <1>dpos
  <2>2. HasDepth(alpha, x, d) =
          (/\ Sig(x) \in Acceptors
           /\ IF d = 0 THEN (IsOneB(x) /\ Fresh(alpha, x))
                       ELSE SigS(Qd(alpha, x, d)) \in Quorums(alpha))
    BY HasDepthDef
  <2> QED BY <2>1, <2>2
<1>base. SigS(W(d-1)) \in Quorums(alpha)  BY <1>hdd, <1>Wd1eq
<1> SUFFICES \A n \in Nat : Q(n)
  <2>1. Q(d-1)  BY <1>dnat
  <2>2. \A i \in 0..(d-1) : SigS(W(i)) \in Quorums(alpha)  BY <2>1, <1>base DEF Q
  <2>3. SigS(W(e-1)) \in Quorums(alpha)  BY <2>2, <1>drange
  <2>4. SigS(Qd(alpha, x, e)) \in Quorums(alpha)  BY <2>3, <1>We1eq
  <2>5. e # 0  BY <1>epos
  <2>6. HasDepth(alpha, x, e) =
          (/\ Sig(x) \in Acceptors
           /\ IF e = 0 THEN (IsOneB(x) /\ Fresh(alpha, x))
                       ELSE SigS(Qd(alpha, x, e)) \in Quorums(alpha))
    BY HasDepthDef
  <2> QED BY <2>4, <1>xSig, <2>5, <2>6
<1> HIDE DEF Q
<1>ind. \A n \in Nat : (\A kk \in 0..(n-1) : Q(kk)) => Q(n)
  <2> USE DEF Q
  <2> SUFFICES ASSUME NEW n \in Nat, \A kk \in 0..(n-1) : Q(kk),
                      SigS(W(n)) \in Quorums(alpha)
               PROVE \A i \in 0..n : SigS(W(i)) \in Quorums(alpha)
    OBVIOUS
  <2>1. CASE n = 0
    <3> SUFFICES ASSUME NEW i \in 0..n PROVE SigS(W(i)) \in Quorums(alpha)  OBVIOUS
    <3>1. i = 0  BY <2>1
    <3> QED BY <3>1, <2>1
  <2>2. CASE n >= 1
    <3>nn. n \in Nat /\ n >= 1  BY <2>2
    <3>step. SigS(W(n-1)) \in Quorums(alpha)
      <4>ne. W(n) # {}
        <5>1. SigS(W(n)) # {}  BY QuorumsHaveMembers
        <5> QED BY <5>1 DEF SigS
      <4>p. PICK p \in W(n) : TRUE  BY <4>ne
      <4>pW. p \in TranExclusive(x) /\ B(p) = B(x) /\ HasDepth(alpha, p, n)  BY <4>p
      <4>pTran. p \in Tran(x) /\ p # x  BY <4>pW DEF TranExclusive
      <4>pMsg. p \in Messages  BY <4>pTran, TranSubMessages
      <4>hd. HasDepth(alpha, p, n) =
               (Sig(p) \in Acceptors /\ SigS(Qd(alpha, p, n)) \in Quorums(alpha))
        <5>1. n # 0  BY <3>nn
        <5>2. HasDepth(alpha, p, n) =
                (/\ Sig(p) \in Acceptors
                 /\ IF n = 0 THEN (IsOneB(p) /\ Fresh(alpha, p))
                             ELSE SigS(Qd(alpha, p, n)) \in Quorums(alpha))
          BY <4>pMsg, HasDepthDef
        <5> QED BY <5>1, <5>2
      <4>quo. SigS(Qd(alpha, p, n)) \in Quorums(alpha)  BY <4>hd, <4>pW
      <4>qd. Qd(alpha, p, n) = {q \in TranExclusive(p) : B(p) = B(q) /\ HasDepth(alpha, q, n-1)}
        BY <3>nn DEF Qd
      <4>sub. Qd(alpha, p, n) \subseteq W(n-1)
        <5> SUFFICES ASSUME NEW q \in Qd(alpha, p, n) PROVE q \in W(n-1)  OBVIOUS
        <5>1. q \in TranExclusive(p) /\ B(p) = B(q) /\ HasDepth(alpha, q, n-1)  BY <4>qd
        <5>2. q \in Tran(p) /\ q # p  BY <5>1 DEF TranExclusive
        <5>3. Tran(p) \subseteq Tran(x)  BY <4>pTran, <4>pMsg DEF TranTrans
        <5>4. q \in Tran(x)  BY <5>2, <5>3
        <5>qnex. q # x
          <6> SUFFICES ASSUME q = x PROVE FALSE  OBVIOUS
          <6>1. x \in Tran(p)  BY <5>2
          <6>2. p \in Tran(x)  BY <4>pTran
          <6>3. p = x  BY <6>1, <6>2, <4>pMsg, TranAntisym
          <6> QED BY <6>3, <4>pTran
        <5>5. q \in TranExclusive(x)  BY <5>4, <5>qnex DEF TranExclusive
        <5>6. B(q) = B(x)  BY <5>1, <4>pW
        <5> QED BY <5>5, <5>6, <5>1
      <4>sigsub. SigS(Qd(alpha, p, n)) \subseteq SigS(W(n-1))  BY <4>sub DEF SigS
      <4>fin. IsFiniteSet(W(n-1))
        <5>1. W(n-1) \subseteq Tran(x)  BY DEF TranExclusive
        <5>2. IsFiniteSet(Tran(x))  BY DEF TranFinite
        <5> QED BY <5>1, <5>2, FS_Subset
      <4>finsig. IsFiniteSet(SigS(W(n-1)))  BY <4>fin, FS_Image DEF SigS
      <4>acc. SigS(W(n-1)) \subseteq Acceptors
        <5> SUFFICES ASSUME NEW aa \in SigS(W(n-1)) PROVE aa \in Acceptors  OBVIOUS
        <5>1. PICK q \in W(n-1) : aa = Sig(q)  BY DEF SigS
        <5>2. HasDepth(alpha, q, n-1)  BY <5>1
        <5>3. Sig(q) \in Acceptors  BY <5>2 DEF HasDepth
        <5> QED BY <5>1, <5>3
      <4> QED BY <4>quo, <4>sigsub, <4>acc, <4>finsig, QuorumUpward
    <3>n1. n-1 \in 0..(n-1)  BY <3>nn
    <3>Qn1. Q(n-1)  BY <3>n1
    <3>below. \A i \in 0..(n-1) : SigS(W(i)) \in Quorums(alpha)  BY <3>Qn1, <3>step
    <3> SUFFICES ASSUME NEW i \in 0..n PROVE SigS(W(i)) \in Quorums(alpha)  OBVIOUS
    <3>a. CASE i = n  BY <3>a
    <3>b. CASE i \in 0..(n-1)  BY <3>b, <3>below
    <3> QED BY <2>2, <3>a, <3>b
  <2> QED BY <2>1, <2>2
<1> QED BY <1>ind, GeneralNatInduction, IsaM("blast")
====================================================================
