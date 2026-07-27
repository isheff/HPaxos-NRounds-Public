------------------------- MODULE ConFromCaughtSym -------------------------
EXTENDS MessageInterface

\* Connectivity is symmetric: the safety sets of {alpha, beta} ARE those of
\* {beta, alpha}.
LEMMA ConFromCaughtSym ==
  ASSUME NEW alpha \in Learners, NEW beta \in Learners, NEW c
  PROVE beta \in ConFromCaught(alpha, c) <=> alpha \in ConFromCaught(beta, c)
<1>eq. {alpha, beta} = {beta, alpha}  OBVIOUS
<1>1. beta \in ConFromCaught(alpha, c) <=> \E s \in SafetySets({alpha, beta}) : s \cap c = {}
  BY DEF ConFromCaught
<1>2. alpha \in ConFromCaught(beta, c) <=> \E s \in SafetySets({beta, alpha}) : s \cap c = {}
  BY DEF ConFromCaught
<1> QED BY <1>1, <1>2, <1>eq
====================================================================
