----------------------------- MODULE CMCFromShape -----------------------------
EXTENDS MessageConcrete, CFiniteSubsetBounded, CMCALUnfold

LEMMA CMCFromShape ==
  ASSUME NEW rec \in [sender : CSenders, payload : CPayload, priors : SUBSET CMC],
         IsFiniteSet(rec.priors)
  PROVE  rec \in CMC
<1>1. rec.priors \subseteq CMC  OBVIOUS
<1>2. \E L \in Nat : \A z \in rec.priors : z \in CMCAL[L]  BY <1>1, CFiniteSubsetBounded
<1> PICK L \in Nat : \A z \in rec.priors : z \in CMCAL[L]  BY <1>2
<1>3. rec.priors \subseteq CMCAL[L]  OBVIOUS
<1>4. rec.priors \in {x2 \in SUBSET CMCAL[L] : IsFiniteSet(x2)}  BY <1>3
<1> DEFINE r == <<rec.sender, rec.payload, rec.priors>>
<1>5. r \in CSenders \X CPayload \X {x2 \in SUBSET CMCAL[L] : IsFiniteSet(x2)}  BY <1>4
<1>6. rec = [sender |-> r[1], payload |-> r[2], priors |-> r[3]]  OBVIOUS
<1>7. rec \in CMCLNew(CMCAL[L])  BY <1>5, <1>6 DEF CMCLNew
<1>8. CMCAL[L+1] = CMCLExt(CMCAL[L])
  <2>1. L + 1 # 0  OBVIOUS
  <2>2. (L+1) - 1 = L  OBVIOUS
  <2> QED BY <2>1, <2>2, CMCALUnfold
<1>9. rec \in CMCAL[L+1]  BY <1>7, <1>8 DEF CMCLExt
<1> QED BY <1>9 DEF CMC
=============================================================================
