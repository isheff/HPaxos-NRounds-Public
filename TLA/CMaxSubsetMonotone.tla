--------------------------- MODULE CMaxSubsetMonotone ---------------------------
\* FiniteSetHasMax and MaxProps come from the LearnerGraphInterface split; Max
\* itself is the shared FiniteSetsExt one reached through MessageConcrete.
EXTENDS MessageConcrete, FiniteSetTheorems, FiniteSetHasMax, MaxProps

LEMMA CMaxSubsetMonotone ==
  ASSUME NEW S1, NEW S2, IsFiniteSet(S2), S1 \subseteq S2, S1 # {}, \A z \in S2 : z \in Nat
  PROVE Max(S1) <= Max(S2)
<1>1. IsFiniteSet(S1)  BY FS_Subset
<1>2. \A z \in S1 : z \in Nat  OBVIOUS
<1>3. \E r \in S1 : \A y \in S1 : y <= r  BY <1>1, FiniteSetHasMax
<1> PICK r1 \in S1 : \A y \in S1 : y <= r1  BY <1>3
<1>4. Max(S1) \in S1 /\ (\A y \in S1 : Max(S1) >= y)  BY <1>1, <1>2, MaxProps
<1>5. \E r \in S2 : \A y \in S2 : y <= r  BY FiniteSetHasMax
<1> PICK r2 \in S2 : \A y \in S2 : y <= r2  BY <1>5
<1>6. Max(S2) \in S2 /\ (\A y \in S2 : Max(S2) >= y)  BY FS_EmptySet, MaxProps
<1>7. Max(S1) \in S2  BY <1>4
<1> QED BY <1>6, <1>7
=============================================================================
