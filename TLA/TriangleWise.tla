------------------------------ MODULE TriangleWise ------------------------------
\* Per-scenario wisdom in the triangle: in each single-failure scenario the
\* designated acceptor is wise -- pa foresees {pc}, pb foresees {pa}, pc
\* foresees {pb}.  (These are the depth-one processes of Lemma 4.4's
\* scenarios; each is served by the embedded HPaxos, see TriangleWiseServed.)
EXTENDS AsymmetricTriangle
LOCAL INSTANCE TLAPS

LEMMA TriangleWise ==
  ASSUME NEW pa, NEW pb, NEW pc, pa # pb, pb # pc, pa # pc
  PROVE  /\ AQWise(TriFPS(pa, pb, pc), pa, {pc})
         /\ AQWise(TriFPS(pa, pb, pc), pb, {pa})
         /\ AQWise(TriFPS(pa, pb, pc), pc, {pb})
<1>v. /\ TriFPS(pa, pb, pc)[pa] = {{pc}}
      /\ TriFPS(pa, pb, pc)[pb] = {{pa}}
      /\ TriFPS(pa, pb, pc)[pc] = {{pb}}
  BY DEF TriFPS
<1> QED  BY <1>v DEF AQWise
====================================================================
