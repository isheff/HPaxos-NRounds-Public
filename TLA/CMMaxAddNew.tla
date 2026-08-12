--------------------------- MODULE CMMaxAddNew ---------------------------
\* Adding a fresh top element to a Tran-closed set: the new element is maximal
\* (Tran-closure would otherwise already have captured it), and the old maximal
\* elements it knocks out are exactly its own priors.
\*
\* This is the "x is genuinely new" branch of the recent_messages update.
EXTENDS HPaxosPlusCalConcrete, CFields, CMessagesSubMC, CTranResolve,
        CSelfInTran, CTranExclRec, TLAPS

LEMMA CMMaxAddNew ==
  ASSUME ConcreteMessageInterface,
         NEW U, U \subseteq Messages, \A z \in U : Tran(z) \subseteq U,
         NEW x \in Messages, x \notin U, TranExclusive(x) \subseteq U
  PROVE  CMMax(U \cup {x}) = (CMMax(U) \ x.priors) \cup {x}
<1>cmi. MessageInterface = CMI
  BY DEF ConcreteMessageInterface
<1>msg. Messages = CMessages
  BY <1>cmi, CFields
<1>xmc. x \in CMC
  BY <1>msg, CMessagesSubMC
<1>xtr. CTranExcl(x) = TranExclusive(x)
  <2>1. Tran(x) = CTran(x)
    BY <1>cmi, <1>msg, CTranResolve
  <2> QED
    BY <2>1 DEF TranExclusive, CTranExcl
<1>xsub. CTranExcl(x) \subseteq U
  BY <1>xtr
\* x.priors need NOT be canonical (no CFilterOut clause pins it); what the
\* argument needs is only that the priors sit inside the strict history and
\* that the strict history decomposes over them (CTranExclRec).
<1>xps. x.priors \subseteq CTranExcl(x)
  <2>1. CPriors(x) \subseteq CTranExcl(x)
    BY <1>xmc, CTranExclRec
  <2> QED BY <2>1 DEF CPriors
<1>xte. CTranExcl(x) = UNION {CTran(p) : p \in x.priors}
  <2>1. CTranExcl(x) = UNION {CTran(p) : p \in CPriors(x)}
    BY <1>xmc, CTranExclRec
  <2> QED BY <2>1 DEF CPriors
\* (i) x is maximal in U \cup {x}: anything above it would already contain it.
<1>xmax. \A y \in U \cup {x} : x \notin CTranExcl(y)
  <2> SUFFICES ASSUME NEW y \in U \cup {x}, x \in CTranExcl(y)
               PROVE  FALSE
    OBVIOUS
  <2>1. y # x
    BY DEF CTranExcl
  <2>2. y \in U
    BY <2>1
  <2>3. Tran(y) = CTran(y)
    BY <1>cmi, <1>msg, <2>2, CTranResolve
  <2>4. x \in Tran(y)
    BY <2>3 DEF CTranExcl
  <2> QED
    BY <2>2, <2>4
\* (ii) the old maximal elements x knocks out are exactly its direct priors.
<1>knock. \A z \in CMMax(U) : z \in CTranExcl(x) <=> z \in x.priors
  <2> SUFFICES ASSUME NEW z \in CMMax(U)
               PROVE  (z \in CTranExcl(x)) <=> (z \in x.priors)
    OBVIOUS
  <2>1. z \in x.priors => z \in CTranExcl(x)
    BY <1>xps
  <2>2. z \in CTranExcl(x) => z \in x.priors
    <3> SUFFICES ASSUME z \in CTranExcl(x), z \notin x.priors
                 PROVE  FALSE
      OBVIOUS
    \* z is below x, hence inside some DIRECT prior's closure; not being that
    \* prior itself, it sits strictly below it -- and the prior lies in U, so
    \* z was never maximal in U.
    <3>1. PICK p \in x.priors : z \in CTran(p)
      BY <1>xte
    <3>2. z # p
      OBVIOUS
    <3>3. z \in CTranExcl(p)
      BY <3>1, <3>2 DEF CTranExcl
    <3>4. p \in U
      BY <3>1, <1>xps, <1>xsub
    <3> QED
      BY <3>3, <3>4 DEF CMMax
  <2> QED
    BY <2>1, <2>2
<1> QED
  BY <1>xmax, <1>knock DEF CMMax
=============================================================================
