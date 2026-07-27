----------------------------- MODULE BalToValDef -----------------------------
EXTENDS ValueConcrete

LEMMA BalToValDef ==
  ASSUME ValueInterface = ValueInterfaceEx, NEW b \in Ballots
  PROVE  BalToVal(b) = IF Unpair[b][2] \in ValuesEx THEN Unpair[b][2] ELSE DefaultValue
  BY DEF BalToVal, ValueInterfaceEx
====================================================================
