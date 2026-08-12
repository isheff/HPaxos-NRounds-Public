-------------------------- MODULE PrevTranCovers --------------------------
\*   PrevTranComplete, PrevTranStruct, DeepestKnownInv, DeepestKnownMaximal,
\*   CaughtMonotoneTran, TranSubMessages -> cited lemmas
\*   TLAPS -> proof-only
EXTENDS RecursiveWellFormed, PrevTranComplete, PrevTranStruct,
        DeepestKnownInv, DeepestKnownMaximal, CaughtMonotoneTran,
        TranSubMessages
LOCAL INSTANCE TLAPS

\* If acceptor Sig(y) is not caught as of w, then y (a Sig(y)-signed message
\* in w's exclusive history) lies on the prevtran chain of w's deepestknown
\* message for Sig(y). The four-way comparison with the chain head: equal
\* (on chain trivially), below (on chain by PrevTranComplete, else Sig(y)
\* would be caught inside), above (impossible by maximality), incomparable
\* (Sig(y) caught at w -- contradiction).
LEMMA PrevTranCovers ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         NEW w \in Messages, NEW y \in TranExclusive(w),
         Sig(y) \in Acceptors, Sig(y) \notin Caught(w)
  PROVE /\ Sig(y) \in DOMAIN DeepestKnown(w)
        /\ y \in PrevTran(DeepestKnown(w)[Sig(y)][2].id)
<1>inv. DeepestKnownInvariant(w)  BY DeepestKnownInv
<1>sdom. Sig(y) \in DOMAIN DeepestKnown(w)
  <2>1. Sig(y) \in SigS(TranExclusive(w))  BY DEF SigS
  <2> QED BY <2>1, <1>inv DEF DeepestKnownInvariant
<1> DEFINE zc == DeepestKnown(w)[Sig(y)][2].id
<1>ze. zc \in TranExclusive(w) /\ Sig(zc) = Sig(y)
  BY <1>inv, <1>sdom DEF DeepestKnownInvariant
<1>zM. zc \in Messages  BY <1>ze, TranSubMessages DEF TranExclusive
<1>yM. y \in Messages  BY TranSubMessages DEF TranExclusive
<1>a. CASE y = zc
  <2>1. zc \in PrevTran(zc)  BY <1>zM, PrevTranStruct
  <2> QED BY <1>a, <2>1, <1>sdom
<1>b. CASE y # zc /\ y \in Tran(zc)
  <2>1. y \in TranExclusive(zc)  BY <1>b DEF TranExclusive
  <2>2. CASE y \in PrevTran(zc)
    <3> QED BY <2>2, <1>sdom
  <2>3. CASE y \notin PrevTran(zc)
    <3>1. Sig(zc) \in Caught(zc)
      BY <2>1, <2>3, <1>ze, <1>zM, PrevTranComplete
    <3>2. zc \in Tran(w)  BY <1>ze DEF TranExclusive
    <3>3. Caught(zc) \subseteq Caught(w)  BY <3>2, CaughtMonotoneTran
    <3>4. Sig(y) \in Caught(w)  BY <3>1, <3>3, <1>ze
    <3> QED BY <3>4
  <2> QED BY <2>2, <2>3
<1>c. CASE y # zc /\ zc \in Tran(y)
  <2>1. zc \in TranExclusive(y)  BY <1>c DEF TranExclusive
  <2> QED BY <2>1, <1>sdom, DeepestKnownMaximal
<1>d. CASE y \notin Tran(zc) /\ zc \notin Tran(y)
  <2>1. y \in Tran(w) /\ zc \in Tran(w)  BY <1>ze DEF TranExclusive
  <2>2. Sig(y) \in CaughtS(Tran(w))  BY <1>d, <2>1, <1>ze DEF CaughtS
  <2>3. Sig(y) \in Caught(w)  BY <2>2 DEF Caught
  <2> QED BY <2>3
<1> QED BY <1>a, <1>b, <1>c, <1>d
====================================================================
