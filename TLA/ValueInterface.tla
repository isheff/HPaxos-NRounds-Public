-------------------------- MODULE ValueInterface --------------------------
\* Naturals supplies Nat (Ballots == Nat) and < (AlwaysAHigherBallot); nothing
\* else here needs an import -- records, functions, \A/\E and the numeric
\* literal 0 are core TLA+.
\*
\* This MUST be EXTENDS rather than LOCAL INSTANCE. Ballots == Nat is an
\* exported definition whose BODY mentions Nat, so a consumer unfolding
\* DEF Ballots must see the same Nat. LOCAL INSTANCE would give this module a
\* private copy, SANY would rename the two apart, and every consumer proof
\* that unfolds Ballots / TypeOKValueInterface / AlwaysAHigherBallot would
\* fail. EXTENDS shares one copy; INSTANCE copies.
\*
\* Dropped from the unsplit version, all unreferenced here: TLAPS (no proofs
\* in this module), FiniteSets, FiniteSetsExt, FiniteSetTheorems.
EXTENDS Naturals

Ballots == Nat
CONSTANT ValueInterface


\* defining the relevant macros
Values == ValueInterface.values
BalToVal(b) == ValueInterface.baltoval[b]

\* assumptions
TypeOKValueInterface ==
  ValueInterface.baltoval \in [Ballots -> Values]
AlwaysAHigherBallot == \A v \in Values: \A b0 \in Ballots:
    \E b1 \in Ballots: b0 < b1 /\ BalToVal(b1) = v
AlwaysAValue == \A b \in Ballots : BalToVal(b) \in Values \* not sure if this is necessary
ValueInterfaceAssumptions ==
    /\ TypeOKValueInterface
    /\ AlwaysAHigherBallot
    /\ AlwaysAValue


====================================================================
