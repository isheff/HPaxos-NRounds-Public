--------------------------- MODULE AsymmetricTriangle ---------------------------
\* The three-process witness from "Symmetry All the Way Down" (Lemma 4.4):
\* canonical quorums  Q_pa = {pa,pb},  Q_pb = {pb,pc},  Q_pc = {pc,pa},
\* i.e. fail-prone systems  F_pa = {{pc}},  F_pb = {{pa}},  F_pc = {{pb}}.
\* Definitions only; lemmas live in Triangle* / NoSymmetricQuorumF1.
EXTENDS AsymmetricQuorums

TriFPS(pa, pb, pc) ==
  [i \in {pa, pb, pc} |->
     IF i = pa THEN {{pc}} ELSE IF i = pb THEN {{pa}} ELSE {{pb}}]

\* The failure patterns leaving at least one process with an all-correct
\* canonical quorum -- F[1] of the depth hierarchy, for the triangle.
TriF1(pa, pb, pc) == {{}, {pa}, {pb}, {pc}}
====================================================================
