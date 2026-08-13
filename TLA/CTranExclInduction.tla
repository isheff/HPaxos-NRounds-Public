-------------------------- MODULE CTranExclInduction --------------------------
\* Well-founded induction over the concrete strict closure: everything in
\* CTranExcl(x) sits at a strictly lower construction level (each prior does,
\* and closures never raise levels), so course-of-values induction on
\* CMinLevel lifts a strict-closure IH to every real message.  This is the
\* concrete counterpart of the interface's TranExclusiveInduction, and the
\* induction principle behind the MemoP (priors-memoized) correctness proofs.
EXTENDS MessageConcrete, FiniteSetTheorems, CMessagesSubMC, CMessageTranClosed,
        CTranExclRec, CTranLevelLE, CMinLevelDom, CPriorsDecreasesLevel
LOCAL INSTANCE TLAPS

THEOREM CTranExclInduction ==
  ASSUME NEW m \in CMessages,
         NEW H(_),
         \A x \in CMessages : (\A y \in CTranExcl(x) : H(y)) => H(x)
  PROVE H(m)
<1> DEFINE lev(z) == CMinLevel(z)
<1> DEFINE Q(n) == \A x \in CMessages : lev(x) = n => H(x)
<1>mnat. lev(m) \in Nat  BY CMessagesSubMC, CMinLevelDom
<1> SUFFICES \A n \in Nat : Q(n)  BY <1>mnat DEF Q
<1> HIDE DEF Q
<1>ind. \A n \in Nat : (\A kk \in 0..(n-1) : Q(kk)) => Q(n)
  <2> USE DEF Q
  <2> SUFFICES ASSUME NEW n \in Nat, \A kk \in 0..(n-1) : Q(kk),
                      NEW x \in CMessages, lev(x) = n
               PROVE  H(x)
    OBVIOUS
  <2>xmc. x \in CMC  BY CMessagesSubMC
  <2>r. \A y \in CTranExcl(x) : H(y)
    <3> SUFFICES ASSUME NEW y \in CTranExcl(x) PROVE H(y)  OBVIOUS
    <3>ycm. y \in CMessages
      <4>1. y \in CTran(x)  BY DEF CTranExcl
      <4> QED BY <4>1, CMessageTranClosed
    <3>ymc. y \in CMC  BY <3>ycm, CMessagesSubMC
    <3>p. PICK p \in CPriors(x) : y \in CTran(p)
      <4>1. CTranExcl(x) = UNION {CTran(q) : q \in CPriors(x)}
        BY <2>xmc, CTranExclRec
      <4> QED BY <4>1
    <3>pmc. p \in CMC
      <4>1. CPriors(x) \subseteq CTranExcl(x)  BY <2>xmc, CTranExclRec
      <4>2. p \in CTran(x)  BY <4>1 DEF CTranExcl
      <4>3. p \in CMessages  BY <4>2, CMessageTranClosed
      <4> QED BY <4>3, CMessagesSubMC
    <3>lp. lev(p) < lev(x)  BY <2>xmc, CPriorsDecreasesLevel
    <3>ly. lev(y) <= lev(p)
      <4>1. CTranBelowProp(p)  BY <3>pmc, CTranLevelLE
      <4> QED BY <4>1, <3>p DEF CTranBelowProp
    <3>nats. lev(y) \in Nat /\ lev(p) \in Nat /\ lev(x) \in Nat
      BY <3>ymc, <3>pmc, <2>xmc, CMinLevelDom
    <3>lt. lev(y) \in 0..(n-1)  BY <3>lp, <3>ly, <3>nats, SMT
    <3> QED BY <3>ycm, <3>lt
  <2> QED BY <2>r
<1> QED BY <1>ind, GeneralNatInduction, IsaM("blast")
=============================================================================
