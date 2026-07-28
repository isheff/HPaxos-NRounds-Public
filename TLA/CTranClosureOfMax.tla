--------------------------- MODULE CTranClosureOfMax ---------------------------
\* The Tran-closure of the maximal antichain of a finite Tran-closed set is
\* that set.  CGenTranRefs is exactly this in Concrete-land; the work here is
\* transporting it across Tran = CTran.
\*
\* Throughout: "U is Tran-closed" means \A z \in U : Tran(z) \subseteq U.
EXTENDS HPaxosPlusCalConcrete, CGenTranRefs, CFields, CMessagesSubMC,
        CTranResolve, TLAPS

LEMMA CTranClosureOfMax ==
  ASSUME ConcreteMessageInterface,
         NEW U, U \subseteq Messages, IsFiniteSet(U),
         \A z \in U : Tran(z) \subseteq U
  PROVE  TranClosure(CMMax(U)) = U
<1>cmi. MessageInterface = CMI
  BY DEF ConcreteMessageInterface
<1>msg. Messages = CMessages
  BY <1>cmi, CFields
<1>mc. U \subseteq CMC
  BY <1>msg, CMessagesSubMC
<1>res. \A z \in U : Tran(z) = CTran(z)
  BY <1>cmi, <1>msg, CTranResolve
<1>cl. \A z \in U : CTran(z) \subseteq U
  BY <1>res
<1>gen. U = UNION {CTran(z) : z \in CMMax(U)}
  BY <1>mc, <1>cl, CGenTranRefs
<1>sub. CMMax(U) \subseteq U
  BY DEF CMMax
<1>eq. UNION {CTran(z) : z \in CMMax(U)} = UNION {Tran(z) : z \in CMMax(U)}
  BY <1>sub, <1>res
<1> QED
  BY <1>gen, <1>eq DEF TranClosure
=============================================================================
