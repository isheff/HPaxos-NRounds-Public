---------------------------- MODULE CRefsSubPriors ----------------------------
\* Any real message's priors sandwich its refs: the maximal elements of the
\* strict closure are always listed among the priors (a maximal element lies
\* in some prior's closure and can only be that prior itself), and the priors
\* always lie inside the strict closure (CTranExclRec).  No canonicality or
\* antichain-ness needed -- this is what lets the S-generalized step lemmas
\* instantiate at S := priors for arbitrary (even byz-sent) messages.
EXTENDS MessageConcrete, CMessagesSubMC, CTranExclRec, CRefsResolve,
        CTranResolve, CMessageTranClosed
LOCAL INSTANCE TLAPS

LEMMA CRefsSubPriors ==
  ASSUME MessageInterface = CMI, NEW x \in CMessages
  PROVE /\ Refs(x) \subseteq x.priors
        /\ x.priors \subseteq TranExclusive(x)
<1>mc. x \in CMC  BY CMessagesSubMC
<1>te. /\ CPriors(x) \subseteq CTranExcl(x)
       /\ CTranExcl(x) = UNION {CTran(p) : p \in CPriors(x)}
  BY <1>mc, CTranExclRec
<1>tr. Tran(x) = CTran(x)  BY CTranResolve
<1>teq. TranExclusive(x) = CTranExcl(x)
  BY <1>tr DEF TranExclusive, CTranExcl
<1>refs. Refs(x) = CRefs(x)  BY CRefsResolve
<1>sub. CRefs(x) \subseteq x.priors
  <2> SUFFICES ASSUME NEW z \in CRefs(x) PROVE z \in x.priors  OBVIOUS
  <2>1. z \in CTranExcl(x)
          /\ \A y \in CTranExcl(x) : y = z \/ z \notin CTran(y)
    BY DEF CRefs
  <2>2. PICK p \in CPriors(x) : z \in CTran(p)  BY <2>1, <1>te
  <2>3. p \in CTranExcl(x)  BY <1>te
  <2>4. p = z \/ z \notin CTran(p)  BY <2>1, <2>3
  <2>5. z = p  BY <2>2, <2>4
  <2> QED BY <2>2, <2>5 DEF CPriors
<1> QED BY <1>sub, <1>refs, <1>te, <1>teq DEF CPriors
=============================================================================
