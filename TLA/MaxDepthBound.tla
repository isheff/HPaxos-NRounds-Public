------------------------- MODULE MaxDepthBound -------------------------
\* Statement mentions Learners / ValidSeqs / Acceptors / MaxDepth
\* (LearnerGraphInterface), Len (Sequences), and Nat. The proof additionally
\* needs Max (to unfold MaxDepth), the FS_* theorems, and MaxProps -- all
\* reached through MaxProps -> FiniteSetsExt / FiniteSetHasMax ->
\* FiniteSetTheorems. Both MaxDepthFinite* lemmas cite this one.
EXTENDS LearnerGraphInterface, Sequences, MaxProps

\* Given a length bound N+1 on all valid chains (from EITHER
\* ValidSeqLenBoundAcceptors or ValidSeqLenBoundLearners) and the fact that
\* <<Acceptors,{}>> is always a valid chain of length 2, MaxDepth(alpha) is
\* sandwiched in 1..N.  Works with the set of lengths L (fully Nat-typed,
\* no subtraction) rather than the set of depths directly, since Len(s)-1
\* for the length-0 (empty) chain is not usefully typed.
LEMMA MaxDepthBound ==
  ASSUME NEW alpha \in Learners, NEW N \in Nat,
         \A l \in ValidSeqs(alpha) : Len(l) <= N + 1,
         <<Acceptors, {}>> \in ValidSeqs(alpha)
  PROVE MaxDepth(alpha) \in 1..N
<1> DEFINE L == {Len(s) : s \in ValidSeqs(alpha)}
<1>witlen. Len(<<Acceptors, {}>>) = 2  OBVIOUS
<1>l2. 2 \in L  BY <1>witlen
<1>rangefin. IsFiniteSet(0..(N+1))  BY FS_Interval
<1>lsub. L \subseteq 0..(N+1)
  <2> SUFFICES ASSUME NEW k \in L PROVE k \in 0..(N+1)  OBVIOUS
  <2>1. PICK s \in ValidSeqs(alpha) : k = Len(s)  OBVIOUS
  <2>2. Len(s) \in Nat  BY <2>1 DEF ValidSeqs
  <2>3. Len(s) <= N + 1  BY <2>1
  <2> QED BY <2>1, <2>2, <2>3
<1>Lfin. IsFiniteSet(L)  BY <1>lsub, <1>rangefin, FS_Subset
<1>Lne. L # {}  BY <1>l2
<1>Lnat. \A x \in L : x \in Nat  BY <1>lsub
<1>maxprops. Max(L) \in L /\ (\A y \in L : Max(L) >= y)  BY <1>Lfin, <1>Lne, <1>Lnat, MaxProps
<1>MaxLinL. Max(L) \in L  BY <1>maxprops
<1>MaxLge2. Max(L) >= 2  BY <1>maxprops, <1>l2
<1>MaxLnat. Max(L) \in Nat  BY <1>MaxLinL, <1>lsub
<1>MaxLle. Max(L) <= N + 1  BY <1>MaxLinL, <1>lsub
<1> PICK sm \in ValidSeqs(alpha) : Len(sm) = Max(L)  BY <1>MaxLinL
<1>smnat. Len(sm) \in Nat  BY DEF ValidSeqs
<1>d_witness. Max(L) - 1 \in {Len(s)-1 : s \in ValidSeqs(alpha)}  OBVIOUS
<1>d_upper. \A d \in {Len(s)-1 : s \in ValidSeqs(alpha)} : d <= Max(L) - 1
  <2> SUFFICES ASSUME NEW d \in {Len(s)-1 : s \in ValidSeqs(alpha)} PROVE d <= Max(L) - 1  OBVIOUS
  <2>1. PICK s \in ValidSeqs(alpha) : d = Len(s)-1  OBVIOUS
  <2>2. Len(s) \in L  BY <2>1
  <2>3. Len(s) <= Max(L)  BY <2>2, <1>maxprops
  <2>4. Len(s) \in Nat  BY <2>1 DEF ValidSeqs
  <2> QED BY <2>1, <2>3, <2>4, <1>MaxLnat
<1>witness2. \E x \in {Len(s)-1 : s \in ValidSeqs(alpha)} : \A y \in {Len(s)-1 : s \in ValidSeqs(alpha)} : x >= y
  BY <1>d_witness, <1>d_upper
<1>maxprops2. MaxDepth(alpha) \in {Len(s)-1 : s \in ValidSeqs(alpha)}
              /\ (\A y \in {Len(s)-1 : s \in ValidSeqs(alpha)} : MaxDepth(alpha) >= y)
  BY <1>witness2 DEF MaxDepth, Max
<1>maxLm1nat. Max(L) - 1 \in Nat  BY <1>MaxLge2, <1>MaxLnat
<1>upper_bnd. Max(L) - 1 <= MaxDepth(alpha)  BY <1>maxprops2, <1>d_witness
<1>lower_bnd. MaxDepth(alpha) <= Max(L) - 1  BY <1>maxprops2, <1>d_upper
<1> PICK sw \in ValidSeqs(alpha) : MaxDepth(alpha) = Len(sw) - 1  BY <1>maxprops2
<1>swnat. Len(sw) \in Nat  BY DEF ValidSeqs
<1>swmd. MaxDepth(alpha) = Len(sw) - 1  OBVIOUS
<1>swge2. Len(sw) >= 2  BY <1>upper_bnd, <1>swnat, <1>maxLm1nat, <1>MaxLge2, <1>MaxLnat, <1>swmd
<1>mdnat. MaxDepth(alpha) \in Nat  BY <1>swge2, <1>swnat
<1> QED BY <1>upper_bnd, <1>lower_bnd, <1>mdnat, <1>MaxLge2, <1>MaxLnat, <1>MaxLle
====================================================================
