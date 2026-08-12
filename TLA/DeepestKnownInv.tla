-------------------------- MODULE DeepestKnownInv --------------------------
\*   DeepestKnownStep, DigestRec, RefsInduction -> cited lemmas
\*   TLAPS -> proof-only
EXTENDS RecursiveWellFormed, DeepestKnownStep, DigestRec, RefsInduction
LOCAL INSTANCE TLAPS

\* Every message satisfies the deepestknown structural invariant:
\* instantiate the generalized step at S := Refs(m) and identify the
\* assembled map with the stored field.
LEMMA DeepestKnownInv ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         NEW m \in Messages
  PROVE DeepestKnownInvariant(m)
<1>cl. \A x \in Messages :
         (\A y \in Refs(x) : DeepestKnownInvariant(y)) => DeepestKnownInvariant(x)
  <2> SUFFICES ASSUME NEW x \in Messages,
                      \A y \in Refs(x) : DeepestKnownInvariant(y)
      PROVE DeepestKnownInvariant(x)
    OBVIOUS
  <2>1. Refs(x) \subseteq TranExclusive(x)  BY DEF Refs
  <2>2. DeepestKnownCorrect(x, DeepestKnownAssemble({Digest(p) : p \in Refs(x)}))
    BY <2>1, DeepestKnownStep
  <2>3. Digest(x) = DigestR(x, {Digest(p) : p \in Refs(x)})  BY DigestRec
  <2>4. DeepestKnown(x) = DeepestKnownAssemble({Digest(p) : p \in Refs(x)})
    BY <2>3 DEF DeepestKnown, DigestR
  <2>5. DeepestKnownCorrect(x, DeepestKnown(x))  BY <2>2, <2>4
  <2> QED BY <2>5 DEF DeepestKnownInvariant, DeepestKnownCorrect
<1> QED BY <1>cl, RefsInduction
====================================================================
