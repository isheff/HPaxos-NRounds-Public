----------------------------- MODULE CDepthDownward -----------------------------
EXTENDS MessageConcrete, CQuorumNonEmpty, CMessagesSubMC, CQdCompute,
        CQuorumUpward, FiniteSetTheorems, NaturalsInduction
LOCAL INSTANCE TLAPS

\* Downward closure: given the depth-j quorum, every lower depth i <= j also
\* has a quorum of ballot-bb signatures in the Tran-closed set U.
LEMMA CDepthDownward ==
  ASSUME LearnersMightAgree, ValidLearnerGraphAssumption,
         NEW U, IsFiniteSet(U), U \subseteq CMessages,
         \A z \in U : CTran(z) \subseteq U,
         NEW alpha \in Learners, NEW bb, NEW j \in Nat,
         CSigS({p \in U : CB(p) = bb /\ CHasDepth(alpha, p, j)}) \in Quorums(alpha)
  PROVE \A i \in 0..j : CSigS({p \in U : CB(p) = bb /\ CHasDepth(alpha, p, i)}) \in Quorums(alpha)
<1> DEFINE W(n) == {p \in U : CB(p) = bb /\ CHasDepth(alpha, p, n)}
<1> DEFINE Q(n) == CSigS(W(n)) \in Quorums(alpha)
                     => \A i \in 0..n : CSigS(W(i)) \in Quorums(alpha)
<1> SUFFICES \A n \in Nat : Q(n)
  <2>1. j \in Nat  OBVIOUS
  <2> QED BY <2>1 DEF Q
<1> HIDE DEF Q
<1>ind. \A n \in Nat : (\A kk \in 0..(n-1) : Q(kk)) => Q(n)
  <2> USE DEF Q
  <2> SUFFICES ASSUME NEW n \in Nat, \A kk \in 0..(n-1) : Q(kk),
                      CSigS(W(n)) \in Quorums(alpha)
               PROVE \A i \in 0..n : CSigS(W(i)) \in Quorums(alpha)
    OBVIOUS
  <2>1. CASE n = 0
    <3> SUFFICES ASSUME NEW i \in 0..n PROVE CSigS(W(i)) \in Quorums(alpha)  OBVIOUS
    <3>1. i = 0  BY <2>1
    <3> QED BY <3>1, <2>1
  <2>2. CASE n >= 1
    <3>nn. n \in Nat /\ n >= 1  BY <2>2
    \* inline downward step: from the depth-n quorum, get the depth-(n-1) quorum
    <3>step. CSigS(W(n-1)) \in Quorums(alpha)
      <4>ne. W(n) # {}
        <5>1. CSigS(W(n)) # {}  BY CQuorumNonEmpty
        <5> QED BY <5>1 DEF CSigS
      <4>p. PICK p \in W(n) : TRUE  BY <4>ne
      <4>pU. p \in U /\ CB(p) = bb /\ CHasDepth(alpha, p, n)  BY <4>p
      <4>pmc. p \in CMC  BY <4>pU, CMessagesSubMC
      <4>hd. CHasDepth(alpha, p, n) =
               (CSig(p) \in Acceptors /\ CSigS(CCfl(p).qd[<<alpha, n>>]) \in Quorums(alpha))
        <5>1. n # 0  BY <3>nn
        <5> QED BY <5>1 DEF CHasDepth
      <4>quo. CSigS(CCfl(p).qd[<<alpha, n>>]) \in Quorums(alpha)  BY <4>hd, <4>pU
      <4>qd. CCfl(p).qd[<<alpha, n>>] = {q \in CTranExcl(p) : CB(q) = CB(p) /\ CHasDepth(alpha, q, n-1)}
        BY <4>pmc, <3>nn, CQdCompute
      <4>sub. CCfl(p).qd[<<alpha, n>>] \subseteq W(n-1)
        <5> SUFFICES ASSUME NEW q \in CCfl(p).qd[<<alpha, n>>] PROVE q \in W(n-1)  OBVIOUS
        <5>1. q \in CTranExcl(p) /\ CB(q) = CB(p) /\ CHasDepth(alpha, q, n-1)  BY <4>qd
        <5>2. q \in CTran(p)  BY <5>1 DEF CTranExcl
        <5>3. CTran(p) \subseteq U  BY <4>pU
        <5>4. q \in U  BY <5>2, <5>3
        <5>5. CB(q) = bb  BY <5>1, <4>pU
        <5> QED BY <5>4, <5>5, <5>1
      <4>sigsub. CSigS(CCfl(p).qd[<<alpha, n>>]) \subseteq CSigS(W(n-1))  BY <4>sub DEF CSigS
      <4>fin. IsFiniteSet(W(n-1))  BY FS_Subset
      <4>finsig. IsFiniteSet(CSigS(W(n-1)))  BY <4>fin, FS_Image DEF CSigS
      <4>acc. CSigS(W(n-1)) \subseteq Acceptors
        <5> SUFFICES ASSUME NEW aa \in CSigS(W(n-1)) PROVE aa \in Acceptors  OBVIOUS
        <5>1. PICK q \in W(n-1) : aa = CSig(q)  BY DEF CSigS
        <5>2. CHasDepth(alpha, q, n-1)  BY <5>1
        <5>3. CSig(q) \in Acceptors  BY <5>2 DEF CHasDepth
        <5> QED BY <5>1, <5>3
      <4> QED BY <4>quo, <4>sigsub, <4>acc, <4>finsig, CQuorumUpward
    <3>n1. n-1 \in 0..(n-1)  BY <2>2
    <3>Qn1. Q(n-1)  BY <3>n1
    <3>below. \A i \in 0..(n-1) : CSigS(W(i)) \in Quorums(alpha)  BY <3>Qn1, <3>step
    <3> SUFFICES ASSUME NEW i \in 0..n PROVE CSigS(W(i)) \in Quorums(alpha)  OBVIOUS
    <3>a. CASE i = n  BY <3>a
    <3>b. CASE i \in 0..(n-1)  BY <3>b, <3>below
    <3> QED BY <2>2, <3>a, <3>b
  <2> QED BY <2>1, <2>2
<1> QED BY <1>ind, GeneralNatInduction, IsaM("blast")
=============================================================================
