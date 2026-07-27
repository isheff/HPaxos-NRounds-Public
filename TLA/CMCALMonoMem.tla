----------------------------- MODULE CMCALMonoMem -----------------------------
EXTENDS MessageConcrete, CMCALMonoGen

LEMMA CMCALMonoMem ==
  ASSUME NEW k \in Nat, NEW l \in Nat, k <= l, NEW z \in CMCAL[k]
  PROVE z \in CMCAL[l]
BY CMCALMonoGen
=============================================================================
