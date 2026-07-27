----------------------- MODULE ValueConcreteTypeOKLemma -----------------------
EXTENDS ValueConcrete, DefaultValInValues, ValuesEq

(* ---------- TypeOKValueInterface ---------- *)
LEMMA ValueConcreteTypeOKLemma ==
  ASSUME ValuesEx # {}, ValuesEx \subseteq Nat, ValueInterface = ValueInterfaceEx
  PROVE  TypeOKValueInterface
  <1>1. DefaultValue \in ValuesEx BY DefaultValInValues
  <1>2. Values = ValuesEx BY ValuesEq
  <1>3. ValueInterface.baltoval
          = [x \in Ballots |-> IF Unpair[x][2] \in ValuesEx THEN Unpair[x][2] ELSE DefaultValue]
    BY DEF ValueInterfaceEx
  <1>4. ASSUME NEW x \in Ballots
        PROVE  (IF Unpair[x][2] \in ValuesEx THEN Unpair[x][2] ELSE DefaultValue) \in ValuesEx
    <2>1. CASE Unpair[x][2] \in ValuesEx
      <3>1. QED BY <2>1
    <2>2. CASE ~(Unpair[x][2] \in ValuesEx)
      <3>1. QED BY <2>2, <1>1
    <2>3. QED BY <2>1, <2>2
  <1>5. ValueInterface.baltoval \in [Ballots -> ValuesEx] BY <1>3, <1>4
  <1>6. QED BY <1>5, <1>2 DEF TypeOKValueInterface
====================================================================
