------------------------------- MODULE ValuesEq -------------------------------
EXTENDS ValueConcrete

LEMMA ValuesEq == ASSUME ValueInterface = ValueInterfaceEx PROVE Values = ValuesEx
  BY DEF Values, ValueInterfaceEx
====================================================================
