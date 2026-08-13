--------------------------- MODULE MemoRecCorrectness ---------------------------
\* THE public reading of the memo record: every field of Memo(m) means what it
\* claims to mean, collected in one statement.  This is the conjunction of the
\* per-field correctness lemmas -- fresh (FreshRec), highesttwoas
\* (HighestTwoAsRec), lrns (LrnsRec), the maxqdepth frontier's own-HasDepth
\* reading (MaxQDepthRec), pendingqd's Qd reading (QdRec), isoneb
\* (IsOneBMemo), the IsTwoA characterization (IsTwoAMemo), and the
\* deepestknown/prevtran chain link (DeepestKnownPrev).
EXTENDS RecursiveWellFormed, FreshRec, HighestTwoAsRec, LrnsRec, MaxQDepthRec,
        QdRec, IsOneBMemo, IsTwoAMemo, DeepestKnownPrev
LOCAL INSTANCE TLAPS

THEOREM MemoRecCorrectness ==
  ASSUME MessageInterfaceAssumptions,
         LearnersMightAgree, ValidLearnerGraphAssumption,
         NEW m \in Messages
  PROVE
    /\ \A alpha \in Learners : MemoFresh(m)[alpha] <=> Fresh(alpha, m)
    /\ HighestTwoAsInvariant(m)
    /\ MemoLrns(m) = Lrns(m)
    /\ Sig(m) \in Acceptors =>
         \A alpha \in Learners : \A d \in Nat :
           d >= 1 =>
             (HasDepth(alpha, m, d) <=>
                (/\ alpha \in DOMAIN MemoMaxQDepth(m)
                 /\ MemoMaxQDepth(m)[alpha] >= 1
                 /\ d <= MemoMaxQDepth(m)[alpha]))
    /\ \A alpha \in DOMAIN MemoMaxQDepth(m) :
         Qd(alpha, m, MemoMaxQDepth(m)[alpha] + 1)
           = MemoPendingQd(m)[alpha] \ {m}
    /\ MemoIsOneB(m) <=> IsOneB(m)
    /\ IsTwoA(m) <=> (~IsProposal(m) /\ MemoLrns(m) # {})
    /\ (Sig(m) \in DOMAIN DeepestKnown(m)) <=> (Prev(m) # {})
    /\ (Sig(m) \in DOMAIN DeepestKnown(m)) =>
         DeepestKnown(m)[Sig(m)][2].id \in Prev(m)
<1>tok. TypeOKMessageInterface  BY DEF MessageInterfaceAssumptions
<1>tf. TranFinite  BY DEF MessageInterfaceAssumptions
<1>tt. TranTrans  BY DEF MessageInterfaceAssumptions
<1>ta. TranAcyclic  BY DEF MessageInterfaceAssumptions
<1>c1. \A alpha \in Learners : MemoFresh(m)[alpha] <=> Fresh(alpha, m)
  <2> SUFFICES ASSUME NEW alpha \in Learners
      PROVE MemoFresh(m)[alpha] <=> Fresh(alpha, m)  OBVIOUS
  <2> QED BY FreshRec
<1>c2. HighestTwoAsInvariant(m)
  BY HighestTwoAsRec
<1>c3. MemoLrns(m) = Lrns(m)
  BY LrnsRec
<1>c4. Sig(m) \in Acceptors =>
         \A alpha \in Learners : \A d \in Nat :
           d >= 1 =>
             (HasDepth(alpha, m, d) <=>
                (/\ alpha \in DOMAIN MemoMaxQDepth(m)
                 /\ MemoMaxQDepth(m)[alpha] >= 1
                 /\ d <= MemoMaxQDepth(m)[alpha]))
  <2>1. CASE Sig(m) \in Acceptors
    <3> SUFFICES ASSUME NEW alpha \in Learners, NEW d \in Nat, d >= 1
        PROVE HasDepth(alpha, m, d) <=>
                (/\ alpha \in DOMAIN MemoMaxQDepth(m)
                 /\ MemoMaxQDepth(m)[alpha] >= 1
                 /\ d <= MemoMaxQDepth(m)[alpha])
      OBVIOUS
    <3> QED BY <2>1, MaxQDepthRec
  <2> QED BY <2>1
<1>c5. \A alpha \in DOMAIN MemoMaxQDepth(m) :
         Qd(alpha, m, MemoMaxQDepth(m)[alpha] + 1)
           = MemoPendingQd(m)[alpha] \ {m}
  <2> SUFFICES ASSUME NEW alpha \in DOMAIN MemoMaxQDepth(m)
      PROVE Qd(alpha, m, MemoMaxQDepth(m)[alpha] + 1)
              = MemoPendingQd(m)[alpha] \ {m}
    OBVIOUS
  <2> QED BY QdRec
<1>c6. MemoIsOneB(m) <=> IsOneB(m)
  BY IsOneBMemo
<1>c7. IsTwoA(m) <=> (~IsProposal(m) /\ MemoLrns(m) # {})
  BY IsTwoAMemo
<1>c89. /\ (Sig(m) \in DOMAIN DeepestKnown(m)) <=> (Prev(m) # {})
        /\ (Sig(m) \in DOMAIN DeepestKnown(m)) =>
             DeepestKnown(m)[Sig(m)][2].id \in Prev(m)
  BY <1>tok, <1>tt, <1>tf, <1>ta, DeepestKnownPrev
<1> QED
  BY <1>c1, <1>c2, <1>c3, <1>c4, <1>c5, <1>c6, <1>c7, <1>c89
=============================================================================
