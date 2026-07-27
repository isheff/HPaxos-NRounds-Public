----------------------------- MODULE CMCALMonoGen -----------------------------
EXTENDS MessageConcrete, CMCALMono, NaturalsInduction

LEMMA CMCALMonoGen ==
  ASSUME NEW k \in Nat, NEW l \in Nat, k <= l
  PROVE CMCAL[k] \subseteq CMCAL[l]
<1> DEFINE Q(n) == \A kk \in Nat : kk <= n => CMCAL[kk] \subseteq CMCAL[n]
<1>base. Q(0)
  <2> QED BY DEF Q
<1>step. \A n \in Nat : Q(n) => Q(n+1)
  <2> SUFFICES ASSUME NEW n \in Nat, Q(n), NEW kk \in Nat, kk <= n+1
               PROVE CMCAL[kk] \subseteq CMCAL[n+1]
    BY DEF Q
  <2>1. CASE kk = n+1
    <3> QED BY <2>1
  <2>2. CASE kk <= n
    <3>1. CMCAL[kk] \subseteq CMCAL[n]  BY <2>2 DEF Q
    <3>2. CMCAL[n] \subseteq CMCAL[n+1]  BY CMCALMono
    <3> QED BY <3>1, <3>2
  <2> QED BY <2>1, <2>2
<1>allQ. \A n \in Nat : Q(n)  BY <1>base, <1>step, NatInduction
<1> QED BY <1>allQ DEF Q
=============================================================================
