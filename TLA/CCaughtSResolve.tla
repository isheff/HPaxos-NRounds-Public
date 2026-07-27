---------------------------- MODULE CCaughtSResolve ----------------------------
EXTENDS MessageConcrete, CSigResolve, CTranResolve

\* Resolve CaughtS on a set entirely inside CMessages.
LEMMA CCaughtSResolve ==
  ASSUME MessageInterface = CMI, NEW S, S \subseteq CMessages
  PROVE CaughtS(S) = CCaughtS(S)
<1>1. CaughtS(S) = {aa \in Acceptors :
        \E m1 \in S : \E m2 \in S :
          /\ Sig(m1) = aa /\ Sig(m2) = aa
          /\ m1 \notin Tran(m2) /\ m2 \notin Tran(m1)}
  BY DEF CaughtS
<1>2. \A m1 \in S : \A m2 \in S : Sig(m1) = CSig(m1) /\ Sig(m2) = CSig(m2)
  BY CSigResolve
<1>3. \A m1 \in S : \A m2 \in S : Tran(m1) = CTran(m1) /\ Tran(m2) = CTran(m2)
  BY CTranResolve
<1> QED BY <1>1, <1>2, <1>3 DEF CCaughtS
=============================================================================
