-------------------------- MODULE ValueInterface --------------------------
EXTENDS Naturals, TLAPS
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE FiniteSetsExt
LOCAL INSTANCE FiniteSetTheorems

Ballots == Nat
MinBallot == 0
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


