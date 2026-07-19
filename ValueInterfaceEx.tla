-------------------------- MODULE ValueInterfaceEx --------------------------
EXTENDS ValueInterface
LOCAL INSTANCE CantorPairing

CONSTANT ValuesEx
\* defining the main example
DefaultValue == CHOOSE x \in ValuesEx : TRUE
ValueInterfaceEx == [
  values   |-> ValuesEx,
  baltoval |-> [x \in Ballots |->
    IF Unpair[x][2] \in ValuesEx
    THEN Unpair[x][2]
    ELSE DefaultValue]]

(* ---------- helper facts about the example interface ---------- *)

LEMMA DefaultValInValues == ASSUME ValuesEx # {} PROVE DefaultValue \in ValuesEx
  BY DEF DefaultValue

LEMMA ValuesEq == ASSUME ValueInterface = ValueInterfaceEx PROVE Values = ValuesEx
  BY DEF Values, ValueInterfaceEx

LEMMA BalToValDef ==
  ASSUME ValueInterface = ValueInterfaceEx, NEW b \in Ballots
  PROVE  BalToVal(b) = IF Unpair[b][2] \in ValuesEx THEN Unpair[b][2] ELSE DefaultValue
  BY DEF BalToVal, ValueInterfaceEx

(* ---------- TypeOKValueInterface ---------- *)
LEMMA TypeOKLemma ==
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

(* ---------- AlwaysAValue ---------- *)
LEMMA ValueLemma ==
  ASSUME ValuesEx # {}, ValuesEx \subseteq Nat, ValueInterface = ValueInterfaceEx
  PROVE  AlwaysAValue
  <1>1. TypeOKValueInterface BY TypeOKLemma
  <1>2. ASSUME NEW b \in Ballots PROVE BalToVal(b) \in Values
    <2>1. ValueInterface.baltoval \in [Ballots -> Values] BY <1>1 DEF TypeOKValueInterface
    <2>2. ValueInterface.baltoval[b] \in Values BY <2>1
    <2>3. QED BY <2>2 DEF BalToVal
  <1>3. QED BY <1>2 DEF AlwaysAValue

(* ---------- AlwaysAHigherBallot ----------
   Given a value v and ballot b0, the ballot b1 = Encode[<<b0+1, v>>] satisfies
   Unpair[b1] = <<b0+1, v>> (so its value is v) and b1 >= (b0+1)+2v > b0. *)
LEMMA HigherLemma ==
  ASSUME ValuesEx # {}, ValuesEx \subseteq Nat, ValueInterface = ValueInterfaceEx
  PROVE  AlwaysAHigherBallot
  <1>1. Values = ValuesEx BY ValuesEq
  <1>2. SUFFICES ASSUME NEW v \in Values, NEW b0 \in Ballots
                 PROVE  \E b1 \in Ballots : b0 < b1 /\ BalToVal(b1) = v
    BY DEF AlwaysAHigherBallot
  <1>3. v \in Nat BY <1>1
  <1>4. b0 \in Nat BY DEF Ballots
  <1>5. b0 + 1 \in Nat BY <1>4
  <1>6. <<b0 + 1, v>> \in Pairs BY <1>3, <1>5 DEF Pairs
  <1>7. Encode[<<b0 + 1, v>>] \in Nat BY <1>6, EncodeType
  <1>8. Encode[<<b0 + 1, v>>] \in Ballots BY <1>7 DEF Ballots
  <1>9. Unpair[Encode[<<b0 + 1, v>>]][2] = v
    <2>1. Unpair[Encode[<<b0 + 1, v>>]] = <<b0 + 1, v>> BY <1>6, UnpairEncode
    <2>2. QED BY <2>1
  <1>10. b0 < Encode[<<b0 + 1, v>>]
    <2>1. Encode[<<b0 + 1, v>>] = Tri[(b0 + 1) + v] + v BY <1>3, <1>5, EncodeVal
    <2>2. (b0 + 1) + v \in Nat BY <1>3, <1>5
    <2>3. Tri[(b0 + 1) + v] >= (b0 + 1) + v BY <2>2, TriGeId
    <2>4. Tri[(b0 + 1) + v] \in Nat BY <2>2, TriNat
    <2>5. QED BY <2>1, <2>3, <2>4, <1>3, <1>4, SMT
  <1>11. BalToVal(Encode[<<b0 + 1, v>>]) = v
    <2>1. v \in ValuesEx BY <1>1
    <2>2. BalToVal(Encode[<<b0 + 1, v>>])
            = IF Unpair[Encode[<<b0 + 1, v>>]][2] \in ValuesEx
              THEN Unpair[Encode[<<b0 + 1, v>>]][2] ELSE DefaultValue
      BY <1>8, BalToValDef
    <2>3. QED BY <2>2, <1>9, <2>1
  <1>12. QED BY <1>8, <1>10, <1>11

THEOREM ValuesInterfaceExSupportsAssumptions ==
    ( /\ ValuesEx # {}
      /\ ValuesEx \subseteq Nat
      /\ ValueInterface = ValueInterfaceEx
    ) => ValueInterfaceAssumptions
  BY TypeOKLemma, HigherLemma, ValueLemma DEF ValueInterfaceAssumptions

====================================================================
