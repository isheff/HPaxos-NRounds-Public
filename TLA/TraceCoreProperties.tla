------------------------ MODULE TraceCoreProperties ------------------------
\*   FiniteSetTheorems -> GeneralNatInduction
\*   TranClosureClosed, ConMonotoneTran -> cited lemmas
\*   TLAPS             -> IsaM; proof-only
EXTENDS MessageInterface, FiniteSetTheorems,
        TranClosureClosed, ConMonotoneTran
LOCAL INSTANCE TLAPS

\* Structural consequences of the core conditions: the chain lives in the
\* closure, the rr_x descend along Tran, and their connectivity sets strictly
\* grow (item 5 supplies growth witnesses one index ahead, hence j < K).
LEMMA TraceCoreProperties ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions,
         NEW mset \in SUBSET Messages,
         NEW alpha \in Learners, NEW lobal \in Ballots,
         NEW himsg \in TranClosure(mset),
         NEW K \in Nat,
         NEW seq \in [1..K -> TraceElem],
         \A x \in 1..K : TraceCondCore(alpha, lobal, TranClosure(mset), himsg, seq, x)
  PROVE /\ \A i \in 1..K : /\ seq[i].mm \in TranClosure(mset)
                           /\ seq[i].rr \in TranClosure(mset)
                           /\ seq[i].ss \in TranClosure(mset)
        /\ \A i, j \in 1..K : i < j => seq[j].rr \in Tran(seq[i].rr)
        /\ \A i, j \in 1..K : (i < j /\ j < K) =>
             /\ Con(alpha, seq[i].rr) \subseteq Con(alpha, seq[j].rr)
             /\ Con(alpha, seq[i].rr) # Con(alpha, seq[j].rr)
<1>mi. TypeOKMessageInterface /\ TranFinite /\ TranTrans /\ TranAcyclic /\ AlwaysAProposal
  BY DEF MessageInterfaceAssumptions
<1>hmMsg. himsg \in Messages /\ Tran(himsg) \subseteq TranClosure(mset)  BY <1>mi, TranClosureClosed
<1>elt. \A i \in 1..K :
          /\ seq[i].mm \in TranClosure(mset)
          /\ seq[i].rr \in TranClosure(mset)
          /\ seq[i].ss \in TranClosure(mset)
  <2> SUFFICES ASSUME NEW i \in 1..K
               PROVE /\ seq[i].mm \in TranClosure(mset)
                     /\ seq[i].rr \in TranClosure(mset)
                     /\ seq[i].ss \in TranClosure(mset)
    OBVIOUS
  <2>cc. TraceCondCore(alpha, lobal, TranClosure(mset), himsg, seq, i)  OBVIOUS
  <2>mm. seq[i].mm \in Tran(himsg)  BY <2>cc DEF TraceCondCore
  <2>mmTC. seq[i].mm \in TranClosure(mset)  BY <2>mm, <1>hmMsg
  <2>mmMsg. seq[i].mm \in Messages /\ Tran(seq[i].mm) \subseteq TranClosure(mset)
    BY <2>mmTC, <1>mi, TranClosureClosed
  <2>rr. seq[i].rr \in Qd(seq[i].gamma, seq[i].mm, 1)  BY <2>cc DEF TraceCondCore
  <2>rrTE. seq[i].rr \in TranExclusive(seq[i].mm)  BY <2>rr DEF Qd
  <2>rrTran. seq[i].rr \in Tran(seq[i].mm)  BY <2>rrTE DEF TranExclusive
  <2>rrTC. seq[i].rr \in TranClosure(mset)  BY <2>rrTran, <2>mmMsg
  <2>rrMsg. seq[i].rr \in Messages /\ Tran(seq[i].rr) \subseteq TranClosure(mset)
    BY <2>rrTC, <1>mi, TranClosureClosed
  <2>ss. seq[i].ss \in Tran(seq[i].rr)  BY <2>cc DEF TraceCondCore
  <2>ssTC. seq[i].ss \in TranClosure(mset)  BY <2>ss, <2>rrMsg
  <2> QED BY <2>mmTC, <2>rrTC, <2>ssTC
<1>eltMsg. \A i \in 1..K : seq[i].mm \in Messages /\ seq[i].rr \in Messages /\ seq[i].ss \in Messages
  <2> SUFFICES ASSUME NEW i \in 1..K
               PROVE seq[i].mm \in Messages /\ seq[i].rr \in Messages /\ seq[i].ss \in Messages
    OBVIOUS
  <2> QED BY <1>elt, <1>mi, TranClosureClosed
<1>onestep. \A i \in 1..(K-1) : seq[i+1].rr \in Tran(seq[i].rr)
  <2> SUFFICES ASSUME NEW i \in 1..(K-1) PROVE seq[i+1].rr \in Tran(seq[i].rr)  OBVIOUS
  <2>i1dom. i+1 \in 1..K  OBVIOUS
  <2>cc. TraceCondCore(alpha, lobal, TranClosure(mset), himsg, seq, i+1)  BY <2>i1dom
  <2>gt1. i+1 > 1  OBVIOUS
  <2>mm. seq[i+1].mm \in Tran(seq[i].rr)  BY <2>cc, <2>gt1 DEF TraceCondCore
  <2>rr. seq[i+1].rr \in Qd(seq[i+1].gamma, seq[i+1].mm, 1)  BY <2>cc DEF TraceCondCore
  <2>rrTE. seq[i+1].rr \in TranExclusive(seq[i+1].mm)  BY <2>rr DEF Qd
  <2>rrTran. seq[i+1].rr \in Tran(seq[i+1].mm)  BY <2>rrTE DEF TranExclusive
  <2>iInK. i \in 1..K  OBVIOUS
  <2>iMsg. seq[i].rr \in Messages  BY <2>iInK, <1>elt, <1>mi, TranClosureClosed
  <2>trans. Tran(seq[i+1].mm) \subseteq Tran(seq[i].rr)  BY <2>mm, <2>iMsg, <1>mi DEF TranTrans
  <2> QED BY <2>rrTran, <2>trans
<1>chain. \A i \in 1..K : \A j \in 1..K : i <= j => seq[j].rr \in Tran(seq[i].rr)
  <2> DEFINE Q(d) == \A i \in 1..K : (i+d \in 1..K) => seq[i+d].rr \in Tran(seq[i].rr)
  <2> SUFFICES \A d \in Nat : Q(d)
    <3> SUFFICES ASSUME NEW i \in 1..K, NEW j \in 1..K, i <= j
                 PROVE seq[j].rr \in Tran(seq[i].rr)
      OBVIOUS
    <3>1. j - i \in Nat  OBVIOUS
    <3>2. Q(j-i)  BY <3>1
    <3>3. i + (j-i) \in 1..K  OBVIOUS
    <3> QED BY <3>2, <3>3
  <2> HIDE DEF Q
  <2>ind. \A d \in Nat : (\A k \in 0..(d-1) : Q(k)) => Q(d)
    <3> USE DEF Q
    <3> SUFFICES ASSUME NEW d \in Nat, \A k \in 0..(d-1) : Q(k),
                        NEW i \in 1..K, i+d \in 1..K
                 PROVE seq[i+d].rr \in Tran(seq[i].rr)
      OBVIOUS
    <3>a. CASE d = 0
      <4>1. i + d = i  BY <3>a
      <4> QED BY <4>1 DEF Tran
    <3>b. CASE d >= 1
      <4>i1dom. i + 1 \in 1..K  BY <3>b
      <4>dm1nat. d - 1 \in Nat /\ d - 1 \in 0..(d-1)  BY <3>b
      <4>ih. Q(d-1)  BY <4>dm1nat
      <4>sum. (i+1) + (d-1) \in 1..K
        <5>1. (i+1) + (d-1) = i + d  BY <3>b
        <5> QED BY <5>1
      <4>rec. seq[(i+1)+(d-1)].rr \in Tran(seq[i+1].rr)  BY <4>ih, <4>i1dom, <4>sum
      <4>eq. (i+1) + (d-1) = i + d  BY <3>b
      <4>onestepAt. seq[i+1].rr \in Tran(seq[i].rr)
        <5>1. i \in 1..(K-1)  BY <3>b, <4>i1dom
        <5> QED BY <5>1, <1>onestep
      <4>rMsg. seq[i+1].rr \in Messages  BY <4>i1dom, <1>eltMsg
      <4>iMsg. seq[i].rr \in Messages  BY <1>eltMsg
      <4>trans. Tran(seq[i+1].rr) \subseteq Tran(seq[i].rr)
        BY <4>onestepAt, <4>iMsg, <1>mi DEF TranTrans
      <4> QED BY <4>rec, <4>eq, <4>trans
    <3> QED BY <3>a, <3>b
  <2> QED BY <2>ind, GeneralNatInduction, IsaM("blast")
<1>bpart. \A i, j \in 1..K : i < j => seq[j].rr \in Tran(seq[i].rr)
  <2> SUFFICES ASSUME NEW i \in 1..K, NEW j \in 1..K, i < j
               PROVE seq[j].rr \in Tran(seq[i].rr)  OBVIOUS
  <2>1. i <= j  OBVIOUS
  <2> QED BY <2>1, <1>chain
<1>submono. \A i \in 1..K : \A j \in 1..K : i <= j => Con(alpha, seq[i].rr) \subseteq Con(alpha, seq[j].rr)
  <2> SUFFICES ASSUME NEW i \in 1..K, NEW j \in 1..K, i <= j
               PROVE Con(alpha, seq[i].rr) \subseteq Con(alpha, seq[j].rr)
    OBVIOUS
  <2>1. CASE i = j  BY <2>1
  <2>2. CASE i < j
    <3>1. seq[j].rr \in Tran(seq[i].rr)  BY <1>chain, <2>2
    <3>2. seq[i].rr \in Messages  BY <1>elt, <1>mi, TranClosureClosed
    <3> QED BY <3>1, <3>2, <1>mi, ConMonotoneTran
  <2> QED BY <2>1, <2>2
<1>cpart. \A i, j \in 1..K : (i < j /\ j < K) =>
             /\ Con(alpha, seq[i].rr) \subseteq Con(alpha, seq[j].rr)
             /\ Con(alpha, seq[i].rr) # Con(alpha, seq[j].rr)
  <2> SUFFICES ASSUME NEW i \in 1..K, NEW j \in 1..K, i < j, j < K
               PROVE /\ Con(alpha, seq[i].rr) \subseteq Con(alpha, seq[j].rr)
                     /\ Con(alpha, seq[i].rr) # Con(alpha, seq[j].rr)
    OBVIOUS
  <2>sub. Con(alpha, seq[i].rr) \subseteq Con(alpha, seq[j].rr)  BY <1>submono
  <2>j1dom. j + 1 \in 1..K  OBVIOUS
  <2>jm1dom. j - 1 \in 1..K  OBVIOUS
  <2>cc. TraceCondCore(alpha, lobal, TranClosure(mset), himsg, seq, j+1)  BY <2>j1dom
  <2>g5. seq[j+1].gamma \in Con(alpha, seq[j].rr)
    <3>1. j + 1 > 1  OBVIOUS
    <3> QED BY <2>cc, <3>1 DEF TraceCondCore
  <2>g6. seq[j+1].gamma \notin Con(alpha, seq[j-1].rr)
    <3>1. j + 1 > 2  OBVIOUS
    <3> QED BY <2>cc, <3>1 DEF TraceCondCore
  <2>subij. Con(alpha, seq[i].rr) \subseteq Con(alpha, seq[j-1].rr)
    <3>1. i <= j - 1  OBVIOUS
    <3> QED BY <1>submono, <3>1, <2>jm1dom
  <2>notmem. seq[j+1].gamma \notin Con(alpha, seq[i].rr)
    <3> SUFFICES ASSUME seq[j+1].gamma \in Con(alpha, seq[i].rr) PROVE FALSE  OBVIOUS
    <3>1. seq[j+1].gamma \in Con(alpha, seq[j-1].rr)  BY <2>subij
    <3> QED BY <3>1, <2>g6
  <2>diff. Con(alpha, seq[i].rr) # Con(alpha, seq[j].rr)  BY <2>g5, <2>notmem
  <2> QED BY <2>sub, <2>diff
<1> QED BY <1>elt, <1>bpart, <1>cpart
====================================================================
