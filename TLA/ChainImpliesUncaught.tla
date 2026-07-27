------------------------ MODULE ChainImpliesUncaught ------------------------
EXTENDS HPaxosPlusCal

LEMMA ChainImpliesUncaught ==
  SafeAcceptorChainInv => SafeAcceptorsUncaughtInvariant
<1> SUFFICES ASSUME SafeAcceptorChainInv
             PROVE SafeAcceptorsUncaughtInvariant
  OBVIOUS
<1> SUFFICES ASSUME SafeAcceptors \cap CaughtS(Msgs) # {} PROVE FALSE
  BY DEF SafeAcceptorsUncaughtInvariant
<1>1. PICK s \in SafeAcceptors \cap CaughtS(Msgs) : TRUE  OBVIOUS
<1>2. s \in SafeAcceptors /\ s \in CaughtS(Msgs)  BY <1>1
<1>3. \E m1 \in Msgs : \E m2 \in Msgs :
        Sig(m1) = s /\ Sig(m2) = s /\ m1 \notin Tran(m2) /\ m2 \notin Tran(m1)
  BY <1>2 DEF CaughtS
<1>4. PICK m1 \in Msgs : \E m2 \in Msgs :
        Sig(m1) = s /\ Sig(m2) = s /\ m1 \notin Tran(m2) /\ m2 \notin Tran(m1)
  BY <1>3
<1>5. PICK m2 \in Msgs :
        Sig(m1) = s /\ Sig(m2) = s /\ m1 \notin Tran(m2) /\ m2 \notin Tran(m1)
  BY <1>4
<1>comp. m1 \in Tran(m2) \/ m2 \in Tran(m1)  BY <1>2, <1>5 DEF SafeAcceptorChainInv
<1> QED BY <1>comp, <1>5
====================================================================
