----------------------------- MODULE ValueLemma -----------------------------
EXTENDS ValueConcrete, ValueConcreteTypeOKLemma

(* ---------- AlwaysAValue ---------- *)
LEMMA ValueLemma ==
  ASSUME ValuesEx # {}, ValuesEx \subseteq Nat, ValueInterface = ValueInterfaceEx
  PROVE  AlwaysAValue
  <1>1. TypeOKValueInterface BY ValueConcreteTypeOKLemma
  <1>2. ASSUME NEW b \in Ballots PROVE BalToVal(b) \in Values
    <2>1. ValueInterface.baltoval \in [Ballots -> Values] BY <1>1 DEF TypeOKValueInterface
    <2>2. ValueInterface.baltoval[b] \in Values BY <2>1
    <2>3. QED BY <2>2 DEF BalToVal
  <1>3. QED BY <1>2 DEF AlwaysAValue
====================================================================
