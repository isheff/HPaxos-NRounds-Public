--------------------------- MODULE HasDepthDef ---------------------------
EXTENDS MessageInterface, FreshDef, QdDef

\* HasDepth is defined directly via the raw CombinedFreshQdLrnsId fields;
\* this shows it agrees with the "nice formula" Fresh/Qd operators, by
\* substituting FreshDef and QdDef into HasDepth's own definition.
THEOREM HasDepthDef ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         NEW alpha \in Learners, NEW x \in Messages, NEW d \in Nat
  PROVE HasDepth(alpha, x, d) =
          /\ Sig(x) \in Acceptors
          /\ IF d=0 THEN (IsOneB(x) /\ Fresh(alpha, x))
                    ELSE SigS(Qd(alpha, x, d)) \in Quorums(alpha)
<1>f. Fresh(alpha, x) = CombinedFreshQdLrnsId(x).fresh[alpha]  BY FreshDef
<1>q. Qd(alpha, x, d) = CombinedFreshQdLrnsId(x).qd[<<alpha, d>>]  BY QdDef
<1> QED BY <1>f, <1>q DEF HasDepth
====================================================================
