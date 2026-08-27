--------------------------- MODULE NoSymmetricQuorumF1 ---------------------------
\* The separation witness, impossibility side ("Symmetry All the Way Down",
\* Lemma 4.4): over the triangle's acceptors, NO single symmetric quorum
\* system satisfies consistency and availability across all the failure
\* patterns of TriF1 -- the scenarios that each leave one process at depth
\* one.  Proof: consistency of a quorum with itself against each singleton
\* pattern forces every quorum to have two or more members; availability at
\* each singleton then forces all three two-element quorums into S; and two
\* of those intersect in a single process, which is itself a pattern of TriF1.
EXTENDS AsymmetricTriangle, SymmetricQuorums
LOCAL INSTANCE TLAPS

THEOREM NoSymmetricQuorumF1 ==
  ASSUME NEW pa, NEW pb, NEW pc, pa # pb, pb # pc, pa # pc
  PROVE  ~ \E S \in SUBSET SUBSET {pa, pb, pc} :
             /\ SymConsistency(S, TriF1(pa, pb, pc))
             /\ SymAvailability(S, TriF1(pa, pb, pc))
<1> SUFFICES ASSUME NEW S \in SUBSET SUBSET {pa, pb, pc},
                    SymConsistency(S, TriF1(pa, pb, pc)),
                    SymAvailability(S, TriF1(pa, pb, pc))
             PROVE  FALSE
  OBVIOUS
<1>f1. {} \in TriF1(pa, pb, pc) /\ {pa} \in TriF1(pa, pb, pc)
       /\ {pb} \in TriF1(pa, pb, pc) /\ {pc} \in TriF1(pa, pb, pc)
  BY DEF TriF1
<1>big. \A q \in S : (pa \in q /\ pb \in q) \/ (pb \in q /\ pc \in q) \/ (pa \in q /\ pc \in q)
  <2> SUFFICES ASSUME NEW q \in S
               PROVE  (pa \in q /\ pb \in q) \/ (pb \in q /\ pc \in q) \/ (pa \in q /\ pc \in q)
    OBVIOUS
  <2>sub. q \subseteq {pa, pb, pc}  OBVIOUS
  <2>n0. ~(q \subseteq {})  BY <1>f1 DEF SymConsistency
  <2>na. ~(q \subseteq {pa})  BY <1>f1 DEF SymConsistency
  <2>nb. ~(q \subseteq {pb})  BY <1>f1 DEF SymConsistency
  <2>nc. ~(q \subseteq {pc})  BY <1>f1 DEF SymConsistency
  <2> QED  BY <2>sub, <2>n0, <2>na, <2>nb, <2>nc
<1>qab. {pa, pb} \in S
  <2>q. PICK q \in S : q \cap {pc} = {}  BY <1>f1 DEF SymAvailability
  <2>sub. q \subseteq {pa, pb, pc}  OBVIOUS
  <2>npc. pc \notin q  BY <2>q
  <2>mem. pa \in q /\ pb \in q  BY <2>npc, <1>big
  <2>eq. q = {pa, pb}  BY <2>q, <2>sub, <2>mem
  <2> QED  BY <2>q, <2>eq
<1>qbc. {pb, pc} \in S
  <2>q. PICK q \in S : q \cap {pa} = {}  BY <1>f1 DEF SymAvailability
  <2>sub. q \subseteq {pa, pb, pc}  OBVIOUS
  <2>npa. pa \notin q  BY <2>q
  <2>mem. pb \in q /\ pc \in q  BY <2>npa, <1>big
  <2>eq. q = {pb, pc}  BY <2>q, <2>sub, <2>mem
  <2> QED  BY <2>q, <2>eq
<1>cap. {pa, pb} \cap {pb, pc} = {pb}  OBVIOUS
<1>bad. ~({pa, pb} \cap {pb, pc} \subseteq {pb})
  BY <1>qab, <1>qbc, <1>f1 DEF SymConsistency
<1> QED  BY <1>cap, <1>bad
====================================================================
