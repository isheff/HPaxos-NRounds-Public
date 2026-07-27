--------------------- MODULE UncaughtSameSigComparable ---------------------
EXTENDS MessageInterface

\* An acceptor not caught in a message set has Tran-comparable messages
\* there (immediate from the definition of CaughtS).
LEMMA UncaughtSameSigComparable ==
  ASSUME NEW M, NEW a \in Acceptors, a \notin CaughtS(M),
         NEW x \in M, NEW y \in M, Sig(x) = a, Sig(y) = a
  PROVE x \in Tran(y) \/ y \in Tran(x)
<1> SUFFICES ASSUME x \notin Tran(y), y \notin Tran(x) PROVE FALSE  OBVIOUS
<1>1. a \in CaughtS(M)  BY DEF CaughtS
<1> QED BY <1>1
====================================================================
