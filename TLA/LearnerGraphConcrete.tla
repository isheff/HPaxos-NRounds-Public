------------------------- MODULE LearnerGraphConcrete -------------------------
\* A concrete 4-learner / 9-acceptor learner graph realizing the partitions
\* {12|34}, {1234}, {1|2|3|4}, proven to satisfy LearnerGraphAssumptions.
\* Both LOCAL INSTANCEs of the original are dropped here:
\*   - FiniteSets: no definition below mentions IsFiniteSet, and where the lemma
\*     modules need it they get it transitively through
\*     LearnerGraphInterface -> FiniteSetsExt -> FiniteSets, as ONE shared copy.
\*     Re-introducing it by LOCAL INSTANCE anywhere would resurrect the
\*     IsFiniteSet vs IsFiniteSet_1 split that this tree is built to avoid.
\*   - FiniteSetTheorems: only FS_Subset/FS_Interval need it, so it is EXTENDS'd
\*     by just the five lemma modules that actually cite them.
\* LearnerGraphInterface also supplies Integers transitively (via FiniteSetsExt),
\* which is what makes the 1..9 and 1..4 intervals below well-defined.
EXTENDS LearnerGraphInterface

\* ---- the concrete model ----
\* acceptors 1..9  =  a b c | d e f | g h i   (left/right/cross triangles)
CAcc == 1..9
CLrn == 1..4
CLQ == {{1,2,7,8},{1,3,7,9},{2,3,8,9}}
CRQ == {{4,5,7,8},{4,6,7,9},{5,6,8,9}}
CLG == {{1,2,3},{1,2,9},{1,8,3},{1,8,9},{7,2,3},{7,2,9},{7,8,3},{7,8,9}}
CRG == {{4,5,6},{4,5,9},{4,8,6},{4,8,9},{7,5,6},{7,5,9},{7,8,6},{7,8,9}}
CCG == {{7,8,9}}
CPairs == {{pr[1], pr[2]} : pr \in CLrn \X CLrn}
CQuorums == [l \in CLrn |-> IF l \in {1,2} THEN CLQ ELSE CRQ]
CSafety  == [p \in CPairs |-> IF p \subseteq {1,2} THEN CLG
                              ELSE IF p \subseteq {3,4} THEN CRG ELSE CCG]
CLGI == [learners |-> CLrn, acceptors |-> CAcc, safety_sets |-> CSafety, quorums |-> CQuorums]
=============================================================================
