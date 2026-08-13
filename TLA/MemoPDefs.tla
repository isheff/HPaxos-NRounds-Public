------------------------------- MODULE MemoPDefs -------------------------------
\* Definitions only: the correctness motive for the priors-recursive MemoP.
\* MemoPGood collects, for a real message m, everything the candidate check
\* and the hereditary step arguments ever read off a stored MemoP record:
\* the value-determined fields agree with their semantic meanings (hence with
\* Memo's fields), the highesttwoas entries are right IN PROJECTION (domain
\* and ballot -- the witness record itself is CHOOSE-tie-sensitive and never
\* read beyond its ballot), the deepestknown map is correct with
\* MemoP-canonical entries (DeepestKnownCorrectP), and the prevtran chain has
\* the five chain properties (struct / absorb / chain / complete / covers).
\* Fields fresh and isoneb are deliberately absent: no assembly and no check
\* ever reads them off a MEMBER record.
EXTENDS WellFormedRecDef

DeepestKnownCorrectP(m, dk) ==
  /\ DOMAIN dk = SigS(TranExclusive(m))
  /\ \A s \in DOMAIN dk :
       /\ dk[s][2] = MemoP(dk[s][2].id)
       /\ dk[s][2].id \in TranExclusive(m)
       /\ Sig(dk[s][2].id) = s
       /\ dk[s][1] \in Nat
       /\ dk[s] = <<DeepestKnownDepth(s, dk[s][2].id), dk[s][2]>>
       /\ \A w \in TranExclusive(m) : Sig(w) = s =>
            /\ DeepestKnownDepth(s, w) \in Nat
            /\ DeepestKnownDepth(s, w) <= dk[s][1]

MemoPGood(m) ==
  /\ MemoP(m).id = m
  /\ MemoP(m).bal = B(m)
  /\ (MemoP(m).newbal <=> (\A y \in Refs(m) : B(y) < B(m)))
  /\ MemoP(m).caught = Caught(m)
  /\ MemoP(m).lrns = Lrns(m)
  /\ MaxQDepthCorrect(m, MemoP(m).maxqdepth, MemoP(m).pendingqd)
  /\ DOMAIN MemoP(m).highesttwoas
       = {l \in Learners : \E y \in TranExclusive(m) : l \in Lrns(y)}
  /\ \A l \in DOMAIN MemoP(m).highesttwoas :
       /\ \E y \in TranExclusive(m) :
            l \in Lrns(y) /\ B(y) = MemoP(m).highesttwoas[l].bal
       /\ \A y \in TranExclusive(m) :
            l \in Lrns(y) => B(y) <= MemoP(m).highesttwoas[l].bal
  /\ DeepestKnownCorrectP(m, MemoP(m).deepestknown)
  /\ m \in MemoP(m).prevtran
  /\ MemoP(m).prevtran \subseteq Tran(m)
  /\ \A y \in MemoP(m).prevtran : Sig(y) = Sig(m)
  /\ \A y \in MemoP(m).prevtran : MemoP(y).prevtran \subseteq MemoP(m).prevtran
  /\ \A y1 \in MemoP(m).prevtran : \A y2 \in MemoP(m).prevtran :
       y1 \in Tran(y2) \/ y2 \in Tran(y1)
  /\ Sig(m) \in Acceptors =>
       \A y \in TranExclusive(m) :
         (Sig(y) = Sig(m) /\ y \notin MemoP(m).prevtran)
           => Sig(m) \in Caught(m)
  /\ \A y \in TranExclusive(m) :
       (Sig(y) \in Acceptors /\ Sig(y) \notin Caught(m)) =>
         /\ Sig(y) \in DOMAIN MemoP(m).deepestknown
         /\ y \in MemoP(m).deepestknown[Sig(y)][2].prevtran
=============================================================================
