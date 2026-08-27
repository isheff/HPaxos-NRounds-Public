------------------------------ MODULE TriangleB3 ------------------------------
\* The triangle is a well-formed asymmetric quorum system: typed, nontrivial,
\* and B^3-satisfying.  Each fps[i] is a SINGLETON family, so any commonly
\* foreseen faulty set of an edge {i,j} is inside fi itself, and two singleton
\* fail-prone sets can never cover three distinct acceptors.
EXTENDS AsymmetricTriangle
LOCAL INSTANCE TLAPS

LEMMA TriangleB3 ==
  ASSUME NEW pa, NEW pb, NEW pc, pa # pb, pb # pc, pa # pc,
         Acceptors = {pa, pb, pc}
  PROVE  /\ AQTypeOK(TriFPS(pa, pb, pc))
         /\ AQNonTrivial(TriFPS(pa, pb, pc))
         /\ AQB3(TriFPS(pa, pb, pc))
<1> DEFINE fps == TriFPS(pa, pb, pc)
<1>v. fps[pa] = {{pc}} /\ fps[pb] = {{pa}} /\ fps[pc] = {{pb}}
  BY DEF TriFPS
<1>ty. AQTypeOK(fps)
  BY DEF TriFPS, AQTypeOK
<1>nt. AQNonTrivial(fps)
  BY <1>v DEF AQNonTrivial
<1>b3. AQB3(fps)
  <2> SUFFICES ASSUME NEW i \in Acceptors, NEW j \in Acceptors,
                      NEW fi \in fps[i], NEW fj \in fps[j],
                      NEW fij \in AQCommon(fps, {i, j})
               PROVE  \E a \in Acceptors : a \notin fi /\ a \notin fj /\ a \notin fij
    BY DEF AQB3
  <2>fiv. fi = {pc} \/ fi = {pa} \/ fi = {pb}  BY <1>v
  <2>fjv. fj = {pc} \/ fj = {pa} \/ fj = {pb}  BY <1>v
  <2>ffi. PICK ffi \in fps[i] : fij \subseteq ffi
    <3>1. AQWise(fps, i, fij)  BY DEF AQCommon, AQJointlyWise
    <3> QED  BY <3>1 DEF AQWise
  <2>sing. ffi = fi  BY <1>v
  <2>sub. fij \subseteq fi  BY <2>ffi, <2>sing
  <2>wit. \E a \in Acceptors : a \notin fi /\ a \notin fj
    BY <2>fiv, <2>fjv
  <2> QED  BY <2>wit, <2>sub
<1> QED  BY <1>ty, <1>nt, <1>b3
====================================================================
