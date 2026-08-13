------------------------------ MODULE MemoUDefs ------------------------------
\* Definitions only: U-parameterized correctness predicates for memo
\* assemblies over a PRIOR SET's memos, where no assembling message exists
\* yet.  UU plays the role TranExclusive(x) plays in the (x, S)-generalized
\* step lemmas: for a candidate with priors pr, UU := UNION {Tran(p) : p \in
\* pr} IS the candidate's exclusive closure (CBuiltTran), so these predicates
\* restate the *Correct bodies with TranExclusive(x) replaced by UU.
EXTENDS RecursiveWellFormed

DeepestKnownCorrectU(UU, dk) ==
  /\ DOMAIN dk = SigS(UU)
  /\ \A s \in DOMAIN dk :
       /\ dk[s][2] = Memo(dk[s][2].id)
       /\ dk[s][2].id \in UU
       /\ Sig(dk[s][2].id) = s
       /\ dk[s][1] \in Nat
       /\ dk[s] = <<DeepestKnownDepth(s, dk[s][2].id), dk[s][2]>>
       /\ \A w \in UU : Sig(w) = s =>
            /\ DeepestKnownDepth(s, w) \in Nat
            /\ DeepestKnownDepth(s, w) <= dk[s][1]
=============================================================================
