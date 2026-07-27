------------------------------- MODULE CMCShape -------------------------------
EXTENDS MessageConcrete, CPriorsInMC, CMinLevelDom, CMCALUnfold

LEMMA CMCShape == \A m \in CMC :
  m \in [sender : CSenders, payload : CPayload, priors : SUBSET CMC]
<1> SUFFICES ASSUME NEW m \in CMC
             PROVE m \in [sender : CSenders, payload : CPayload, priors : SUBSET CMC]
  OBVIOUS
<1>pri. m.priors \subseteq CMC  BY CPriorsInMC DEF CPriors
<1> DEFINE lev == CMinLevel(m)
<1>dom. lev \in Nat /\ m \in CMCAL[lev]
        /\ \A k \in Nat : m \in CMCAL[k] => lev <= k  BY CMinLevelDom
<1>2. CASE lev = 0
  <2>1. m \in CMCLBase  BY <1>dom, <1>2, CMCALUnfold
  <2>2. PICK r \in CSenders \X CPayload : m = [sender |-> r[1], payload |-> r[2], priors |-> {}]
    BY <2>1 DEF CMCLBase
  <2>3. m.sender = r[1] /\ m.payload = r[2] /\ r[1] \in CSenders /\ r[2] \in CPayload  BY <2>2
  <2> QED BY <2>2, <2>3, <1>pri
<1>3. CASE lev # 0
  <2>1. lev - 1 \in Nat  BY <1>dom, <1>3
  <2>2. m \notin CMCAL[lev-1]
    <3> SUFFICES ASSUME m \in CMCAL[lev-1] PROVE FALSE  OBVIOUS
    <3>1. lev <= lev - 1  BY <1>dom, <2>1
    <3> QED BY <3>1, <2>1, <1>dom
  <2>3. m \in CMCLExt(CMCAL[lev-1])  BY <1>dom, <1>3, CMCALUnfold
  <2>4. m \in CMCLNew(CMCAL[lev-1])  BY <2>3, <2>2 DEF CMCLExt
  <2>5. PICK r \in CSenders \X CPayload \X {x \in SUBSET CMCAL[lev-1] : IsFiniteSet(x)} :
          m = [sender |-> r[1], payload |-> r[2], priors |-> r[3]]  BY <2>4 DEF CMCLNew
  <2>6. m.sender = r[1] /\ m.payload = r[2] /\ r[1] \in CSenders /\ r[2] \in CPayload  BY <2>5
  <2> QED BY <2>5, <2>6, <1>pri
<1> QED BY <1>2, <1>3
=============================================================================
