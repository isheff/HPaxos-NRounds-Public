------------------ MODULE HPaxosPlusCalConcreteSpecEquivalence ------------------
\* THE THEOREM.  HPaxosPlusCalConcrete is HPaxosPlusCal, exactly, once
\* recent_messages is held to the value it is bookkeeping for.
\*
\* CSpec => Spec is refinement: looking only at Msgs and known_messages -- the
\* variables HPaxosPlusCal declares -- every concrete behaviour is an abstract
\* one, with the same transitions enabled under the same conditions.
\*
\* The converse needs care.  Spec => CSpec is FALSE: CSpec constrains
\* recent_messages, a variable Spec never mentions, so a behaviour of Spec
\* whose recent_messages does something arbitrary satisfies Spec and not CSpec.
\* What holds is that recent_messages is REDUNDANT state, pinned at every
\* instant to a function of Msgs and known_messages alone -- which is what
\* CRecentOK says -- and adding that constraint recovers CSpec exactly.
\*
\* This is the usual "Spec => \EE recent_messages : CSpec" made concrete: the
\* witness is the refinement mapping recent_messages[s] = CMMax(known_messages[s]
\* \cup CSelfSent(s)).  \EE is out of reach for TLAPS, and INSTANCE ... WITH is
\* unusable here (tlapm dies with Expr.Levels: ARITY elaborating
\* MessageInterface's CombinedFreshQdLrnsIdR), so the mapping is stated as a
\* constraint rather than substituted.  Same content either way.
\*
\* The third conjunct, []CSafeSentCanonical, pins the abstract spec's
\* nondeterministic forced-send witness: witnesses agree on their history but
\* not on their priors field, and only the canonical one is the record the
\* concrete spec builds.  It costs nothing on the CSpec side -- honest
\* acceptors always send canonically (CSafeSentCanonicalHolds).
EXTENDS HPaxosPlusCalConcrete, CRefinesAbstract, CAbstractSimulated,
        CJointHolds, CSafeSentCanonicalHolds, TLAPS

THEOREM HPaxosPlusCalConcreteSpecEquivalence ==
  ASSUME ConcreteMessageInterface, SafeAcceptorsAssumption
  PROVE  CSpec <=> (Spec /\ []CRecentOK /\ []CSafeSentCanonical)
<1>1. CSpec => Spec
  BY CRefinesAbstract
<1>2. CSpec => []CJoint
  BY CJointHolds
<1>3. CJoint => CRecentOK
  BY DEF CJoint, CInv, CRecentOK
<1>4. CSpec => []CRecentOK
  BY <1>2, <1>3, PTL
<1>5. CSpec => []CSafeSentCanonical
  <2>1. CSpec => [](\A m \in Msgs :
                      Sig(m) \in SafeAcceptors => m.priors = Refs(m))
    BY CSafeSentCanonicalHolds
  <2>2. (\A m \in Msgs : Sig(m) \in SafeAcceptors => m.priors = Refs(m))
          <=> CSafeSentCanonical
    BY DEF CSafeSentCanonical
  <2> QED BY <2>1, <2>2, PTL
<1>6. (Spec /\ []CRecentOK /\ []CSafeSentCanonical) => CSpec
  BY CAbstractSimulated
<1> QED
  BY <1>1, <1>4, <1>5, <1>6
=============================================================================
