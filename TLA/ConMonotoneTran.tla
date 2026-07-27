-------------------------- MODULE ConMonotoneTran --------------------------
\* ConFromCaughtAntitone comes from the LearnerGraphInterface split; it and
\* MessageInterface share LearnerGraphInterface, so it must be EXTENDS.
EXTENDS MessageInterface, CaughtMonotoneTran, ConFromCaughtAntitone

\* Connectivity only grows when walking to an ancestor.
LEMMA ConMonotoneTran ==
  ASSUME TypeOKMessageInterface, TranTrans, NEW alpha \in Learners,
         NEW x \in Messages, NEW y \in Tran(x)
  PROVE Con(alpha, x) \subseteq Con(alpha, y)
<1>1. Caught(y) \subseteq Caught(x)  BY CaughtMonotoneTran
<1>2. ConFromCaught(alpha, Caught(x)) \subseteq ConFromCaught(alpha, Caught(y))
  BY <1>1, ConFromCaughtAntitone
<1> QED BY <1>2 DEF Con
====================================================================
