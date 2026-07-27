---------------------------- MODULE BMaxExists ----------------------------
EXTENDS MessageInterface, BBallot, FiniteMaxExists

\* A finite nonempty message set has a B-maximal element.  First-order
\* wrapper around FiniteMaxExists (which TLAPS cannot apply directly to a
\* locally-DEFINEd set; same pattern as TranMaxExists).
LEMMA BMaxExists ==
  ASSUME TypeOKMessageInterface, TranFinite, AlwaysAProposal,
         NEW T, IsFiniteSet(T), T # {}, T \subseteq Messages
  PROVE \E r \in T : \A y \in T : B(y) <= B(r)
<1>1. \A z \in T : B(z) \in Nat
  <2> SUFFICES ASSUME NEW z \in T PROVE B(z) \in Nat  OBVIOUS
  <2>1. z \in Messages  OBVIOUS
  <2>2. B(z) \in Ballots  BY <2>1, BBallot
  <2> QED BY <2>2 DEF Ballots
<1> QED BY <1>1, FiniteMaxExists
====================================================================
