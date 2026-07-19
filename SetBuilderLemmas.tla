---------------------- MODULE SetBuilderLemmas ----------------------
EXTENDS Naturals, TLAPS
LEMMA FstProj == ASSUME NEW A, NEW B, NEW e \in A \times B PROVE e[1] \in A  OBVIOUS
LEMMA SndProj == ASSUME NEW A, NEW B, NEW e \in A \times B PROVE e[2] \in B  OBVIOUS
LEMMA PairForm == ASSUME NEW A, NEW B, NEW e \in A \times B PROVE e = <<e[1], e[2]>>  OBVIOUS
====================================================================
