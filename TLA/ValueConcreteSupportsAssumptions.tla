------------------- MODULE ValueConcreteSupportsAssumptions -------------------
EXTENDS ValueConcrete, ValueConcreteTypeOKLemma, HigherLemma, ValueLemma

THEOREM ValueConcreteSupportsAssumptions ==
  (ValuesExAssumption /\ ValueInterface = ValueInterfaceEx)
  => ValueInterfaceAssumptions
  BY ValueConcreteTypeOKLemma, HigherLemma, ValueLemma DEF ValueInterfaceAssumptions, ValuesExAssumption
====================================================================
