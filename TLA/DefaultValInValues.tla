-------------------------- MODULE DefaultValInValues --------------------------
EXTENDS ValueConcrete

LEMMA DefaultValInValues == ASSUME ValuesEx # {} PROVE DefaultValue \in ValuesEx
  BY DEF DefaultValue
====================================================================
