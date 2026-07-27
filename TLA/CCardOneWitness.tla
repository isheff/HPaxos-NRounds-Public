---------------------------- MODULE CCardOneWitness ----------------------------
EXTENDS MessageConcrete, FiniteSetTheorems

\* A finite set of cardinality 1 is a singleton.
LEMMA CCardOneWitness ==
  ASSUME NEW S, IsFiniteSet(S), Cardinality(S) = 1
  PROVE \E s : S = {s}
<1>ne. S # {}  BY FS_EmptySet
<1> PICK s \in S : TRUE  BY <1>ne
<1>rm. IsFiniteSet(S \ {s}) /\ Cardinality(S \ {s}) = 0  BY FS_RemoveElement
<1>empty. S \ {s} = {}  BY <1>rm, FS_EmptySet
<1> QED BY <1>empty
=============================================================================
