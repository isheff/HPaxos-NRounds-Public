------------------------------ MODULE CMCALMono ------------------------------
EXTENDS MessageConcrete, CMCALUnfold

LEMMA CMCALMono ==
  ASSUME NEW l \in Nat
  PROVE CMCAL[l] \subseteq CMCAL[l+1]
<1>1. l + 1 # 0  OBVIOUS
<1>2. (l+1) - 1 = l  OBVIOUS
<1>3. CMCAL[l+1] = CMCLExt(CMCAL[(l+1)-1])  BY <1>1, CMCALUnfold
<1>4. CMCAL[l+1] = CMCLExt(CMCAL[l])  BY <1>2, <1>3
<1> QED BY <1>4 DEF CMCLExt
=============================================================================
