------------------------------ MODULE MemoPUDefs ------------------------------
\* Definitions only: the P-side, U-parameterized correctness predicate.
\* DeepestKnownCorrectUP is DeepestKnownCorrect with TranExclusive(m)
\* replaced by an arbitrary closure UU and with MemoP-canonical
\* entries -- what the deepestknown assembly over a prior set's MemoP
\* records satisfies for the closure UU those priors span (which, by
\* CBuiltTran, IS the candidate's exclusive closure).  Depths stay the
\* ordinary semantic DeepestKnownDepth values.
EXTENDS WellFormedRecDef

DeepestKnownCorrectUP(UU, dk) ==
  /\ DOMAIN dk = SigS(UU)
  /\ \A s \in DOMAIN dk :
       /\ dk[s][2] = MemoP(dk[s][2].id)
       /\ dk[s][2].id \in UU
       /\ Sig(dk[s][2].id) = s
       /\ dk[s][1] \in Nat
       /\ dk[s] = <<DeepestKnownDepth(s, dk[s][2].id), dk[s][2]>>
       /\ \A w \in UU : Sig(w) = s =>
            /\ DeepestKnownDepth(s, w) \in Nat
            /\ DeepestKnownDepth(s, w) <= dk[s][1]
=============================================================================
