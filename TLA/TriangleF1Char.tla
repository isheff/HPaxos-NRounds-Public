----------------------------- MODULE TriangleF1Char -----------------------------
\* TriF1 really is F[1]: over the triangle, a failure pattern leaves some
\* acceptor with an all-correct canonical quorum (equivalently, by the
\* canonical dictionary, leaves some acceptor WISE) exactly when it lies in
\* TriF1 = { {}, {pa}, {pb}, {pc} }.
EXTENDS AsymmetricTriangle
LOCAL INSTANCE TLAPS

THEOREM TriangleF1Char ==
  ASSUME NEW pa, NEW pb, NEW pc, pa # pb, pb # pc, pa # pc,
         NEW ff \in SUBSET {pa, pb, pc}
  PROVE  (ff \in TriF1(pa, pb, pc))
           <=> (\E i \in {pa, pb, pc} : AQWise(TriFPS(pa, pb, pc), i, ff))
<1>v. /\ TriFPS(pa, pb, pc)[pa] = {{pc}}
      /\ TriFPS(pa, pb, pc)[pb] = {{pa}}
      /\ TriFPS(pa, pb, pc)[pc] = {{pb}}
  BY DEF TriFPS
<1>fwd. (ff \in TriF1(pa, pb, pc))
          => (\E i \in {pa, pb, pc} : AQWise(TriFPS(pa, pb, pc), i, ff))
  <2> SUFFICES ASSUME ff \in TriF1(pa, pb, pc)
               PROVE  \E i \in {pa, pb, pc} : AQWise(TriFPS(pa, pb, pc), i, ff)
    OBVIOUS
  <2>c1. CASE ff = {} \/ ff = {pc}
    <3>1. AQWise(TriFPS(pa, pb, pc), pa, ff)  BY <2>c1, <1>v DEF AQWise
    <3> QED  BY <3>1
  <2>c2. CASE ff = {pa}
    <3>1. AQWise(TriFPS(pa, pb, pc), pb, ff)  BY <2>c2, <1>v DEF AQWise
    <3> QED  BY <3>1
  <2>c3. CASE ff = {pb}
    <3>1. AQWise(TriFPS(pa, pb, pc), pc, ff)  BY <2>c3, <1>v DEF AQWise
    <3> QED  BY <3>1
  <2> QED  BY <2>c1, <2>c2, <2>c3 DEF TriF1
<1>bwd. (\E i \in {pa, pb, pc} : AQWise(TriFPS(pa, pb, pc), i, ff))
          => (ff \in TriF1(pa, pb, pc))
  <2> SUFFICES ASSUME NEW i \in {pa, pb, pc}, AQWise(TriFPS(pa, pb, pc), i, ff)
               PROVE  ff \in TriF1(pa, pb, pc)
    OBVIOUS
  <2>f. PICK f \in TriFPS(pa, pb, pc)[i] : ff \subseteq f  BY DEF AQWise
  <2>fv. f = {pa} \/ f = {pb} \/ f = {pc}  BY <2>f, <1>v
  <2>sub. ff \subseteq {pa} \/ ff \subseteq {pb} \/ ff \subseteq {pc}  BY <2>f, <2>fv
  <2> QED  BY <2>sub DEF TriF1
<1> QED  BY <1>fwd, <1>bwd
====================================================================
