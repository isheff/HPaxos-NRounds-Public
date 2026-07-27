------------------------------ MODULE CantorPairing ------------------------------
(***************************************************************************)
(* An isomorphism (bijection) between Nat and pairs of naturals, given by *)
(* the Cantor pairing function, proved correct with TLAPS.               *)
(*                                                                       *)
(*   Encode(<<x,y>>) = Tri[x+y] + y      where Tri[d] = 0+1+...+d        *)
(*          which is = ((x + y) * (x + y + 1)) \div 2 + y (EncodeClosed) *)
(*                                                                       *)
(* Tri (triangular numbers, d*(d+1)/2) is defined recursively so we      *)
(* never need integer division, and the inverse Unpair is defined        *)
(* recursively by walking successive diagonals, so we never need integer *)
(* square roots.  All proofs reduce to induction and linear arithmetic.  *)
(***************************************************************************)
\* NaturalsInduction: NatInductiveDef/NatInductiveDefConclusion/NatInduction appear
\*   in the STATEMENTS of TriDefConclusion and UnpairDefConclusion, so EXTENDS.
\* Functions: Bijection/Injection/Surjection appear in EncodeIsBijection's statement.
\* Integers dropped -- redundant, since NaturalsInduction and Functions each
\*   already EXTENDS it, so Nat/+/*/\div/<= arrive transitively via the SAME copy.
\* TLAPS is proof-only here (Isa, SMT backend pragmas -- never in an exported
\*   definition body), so LOCAL INSTANCE, matching the rest of split/.
EXTENDS NaturalsInduction, Functions
LOCAL INSTANCE TLAPS

Pairs == Nat \X Nat

(* Triangular numbers: Tri[d] = 0 + 1 + ... + d = d*(d+1)/2. *)
Tri[d \in Nat] == IF d = 0 THEN 0 ELSE Tri[d-1] + d

(* Cantor pairing, as a function from Pairs to Nat. *)
Encode == [p \in Pairs |-> Tri[p[1] + p[2]] + p[2]]

(* The inverse, as a function from Nat to Pairs. *)
Unpair[n \in Nat] ==
  IF n = 0 THEN <<0, 0>>
  ELSE IF Unpair[n-1][1] = 0
       THEN <<Unpair[n-1][2] + 1, 0>>
       ELSE <<Unpair[n-1][1] - 1, Unpair[n-1][2] + 1>>

(***************************************************************************)
(* Basic facts about Tri.                                                 *)
(***************************************************************************)


LEMMA TriDefConclusion == NatInductiveDefConclusion(Tri, 0, LAMBDA v, n : v + n)
  <1>1. NatInductiveDefHypothesis(Tri, 0, LAMBDA v, n : v + n)
    BY DEF NatInductiveDefHypothesis, Tri
  <1>2. QED BY <1>1, NatInductiveDef

LEMMA TriRec == \A d \in Nat : Tri[d] = IF d = 0 THEN 0 ELSE Tri[d-1] + d
  BY TriDefConclusion DEF NatInductiveDefConclusion

LEMMA TriType == Tri \in [Nat -> Nat]
  <1>1. \A v \in Nat, n \in Nat \ {0} : v + n \in Nat OBVIOUS
  <1>2. QED BY <1>1, NatInductiveDefType, TriDefConclusion, Isa

LEMMA TriNat == \A d \in Nat : Tri[d] \in Nat
  BY TriType

LEMMA Tri0 == Tri[0] = 0
  BY TriRec

LEMMA TriStep == \A d \in Nat : Tri[d+1] = Tri[d] + (d + 1)
  <1>1. TAKE d \in Nat
  <1>2. d + 1 \in Nat /\ (d + 1) # 0 /\ (d + 1) - 1 = d OBVIOUS
  <1>3. Tri[d+1] = IF (d+1) = 0 THEN 0 ELSE Tri[(d+1)-1] + (d+1)
    BY TriRec, <1>2
  <1>4. QED BY <1>2, <1>3

LEMMA TriMultiplied == \A d \in Nat : 2 * Tri[d] = d * (d + 1)
  <1>1. DEFINE P(n) == 2 * Tri[n] = n * (n + 1)
  <1>2. P(0) BY Tri0
  <1>3. ASSUME NEW n \in Nat, P(n) 
        PROVE P(n+1) 
    BY <1>3, TriStep, TriNat
  <1>4. QED BY <1>2, <1>3, NatInduction

LEMMA TriClosed == \A d \in Nat : Tri[d] = (d * (d + 1)) \div 2
  BY TriMultiplied, TriNat

(***************************************************************************)
(* Encode is a function Pairs -> Nat and evaluates as expected.           *)
(***************************************************************************)
LEMMA EncodeType == Encode \in [Pairs -> Nat]
  <1>1. \A p \in Pairs : Tri[p[1] + p[2]] + p[2] \in Nat
    BY TriNat DEF Pairs
  <1>2. QED BY <1>1 DEF Encode

LEMMA EncodeVal == \A x \in Nat, y \in Nat : Encode[<<x, y>>] = Tri[x + y] + y
  <1>1. TAKE x \in Nat, y \in Nat
  <1>2. <<x, y>> \in Pairs BY DEF Pairs
  <1>3. QED BY <1>2 DEF Encode

LEMMA EncodeClosed == \A x \in Nat, y \in Nat :
  Encode[<<x, y>>] = (((x + y) * (x + y + 1)) \div 2) + y
  BY EncodeVal, TriClosed

(***************************************************************************)
(* Unpair is a function Nat -> Pairs and unfolds as expected.            *)
(***************************************************************************)
LEMMA UnpairDefConclusion ==
  NatInductiveDefConclusion(Unpair, <<0, 0>>,
     LAMBDA v, n : IF v[1] = 0 THEN <<v[2] + 1, 0>> ELSE <<v[1] - 1, v[2] + 1>>)
  <1>1. NatInductiveDefHypothesis(Unpair, <<0, 0>>,
           LAMBDA v, n : IF v[1] = 0 THEN <<v[2] + 1, 0>> ELSE <<v[1] - 1, v[2] + 1>>)
    BY DEF NatInductiveDefHypothesis, Unpair
  <1>2. QED BY <1>1, NatInductiveDef

LEMMA UnpairIsFcn ==
  Unpair = [n \in Nat |->
       IF n = 0 THEN <<0, 0>>
       ELSE IF Unpair[n-1][1] = 0
            THEN <<Unpair[n-1][2] + 1, 0>>
            ELSE <<Unpair[n-1][1] - 1, Unpair[n-1][2] + 1>>]
  BY UnpairDefConclusion DEF NatInductiveDefConclusion

LEMMA Unpair0 == Unpair[0] = <<0, 0>>
  BY UnpairIsFcn

LEMMA UnpairSucc == \A n \in Nat :
    Unpair[n+1] = IF Unpair[n][1] = 0 THEN <<Unpair[n][2] + 1, 0>>
                                       ELSE <<Unpair[n][1] - 1, Unpair[n][2] + 1>>
  <1>1. TAKE n \in Nat
  <1>2. (n+1) \in Nat /\ (n+1) # 0 /\ (n+1) - 1 = n OBVIOUS
  <1>3. QED BY UnpairIsFcn, <1>2

LEMMA UnpairType == Unpair \in [Nat -> Pairs]
  <1> DEFINE P(n) == Unpair[n] \in Pairs
  <1>1. P(0) BY Unpair0 DEF Pairs
  <1>2. ASSUME NEW n \in Nat, P(n) PROVE P(n+1)
    <2>0. SUFFICES Unpair[n+1] \in Pairs BY DEF P
    <2>1. Unpair[n] \in Pairs BY <1>2 DEF P
    <2>2. Unpair[n][1] \in Nat /\ Unpair[n][2] \in Nat BY <2>1 DEF Pairs
    <2>3. Unpair[n+1] = IF Unpair[n][1] = 0 THEN <<Unpair[n][2] + 1, 0>>
                                            ELSE <<Unpair[n][1] - 1, Unpair[n][2] + 1>>
      BY UnpairSucc
    <2>4. QED BY <2>2, <2>3 DEF Pairs
  <1>3. \A n \in Nat : P(n)
    <2> HIDE DEF P
    <2> QED BY <1>1, <1>2, NatInduction, Isa
  <1>4. QED BY <1>3, UnpairIsFcn

(***************************************************************************)
(* Right inverse:  Encode o Unpair = identity on Nat.                     *)
(* (This shows Encode is surjective and Unpair injective.)                *)
(***************************************************************************)
THEOREM EncodeUnpair == \A n \in Nat : Encode[Unpair[n]] = n
  <1> DEFINE P(n) == Encode[Unpair[n]] = n
  <1>1. P(0)
    <2>1. Unpair[0] = <<0, 0>> BY Unpair0
    <2>2. Encode[<<0, 0>>] = Tri[0 + 0] + 0 BY EncodeVal
    <2>3. QED BY <2>1, <2>2, Tri0
  <1>2. ASSUME NEW n \in Nat, P(n) PROVE P(n+1)
    <2>1. Unpair[n] \in Pairs BY UnpairType
    <2>2. /\ Unpair[n][1] \in Nat
          /\ Unpair[n][2] \in Nat
          /\ Unpair[n] = <<Unpair[n][1], Unpair[n][2]>>
      BY <2>1 DEF Pairs
    <2> DEFINE x == Unpair[n][1]
    <2> DEFINE y == Unpair[n][2]
    <2>3. Encode[Unpair[n]] = Tri[x + y] + y BY <2>2, EncodeVal
    <2>4. Tri[x + y] + y = n BY <1>2, <2>3 DEF P
    <2>5. Unpair[n+1] = IF x = 0 THEN <<y + 1, 0>> ELSE <<x - 1, y + 1>>
      BY UnpairSucc
    <2>6. Encode[Unpair[n+1]] = n + 1
      <3>1. CASE x = 0
        <4>1. Unpair[n+1] = <<y + 1, 0>> BY <2>5, <3>1
        <4>2. Encode[Unpair[n+1]] = Tri[(y + 1) + 0] + 0 BY <4>1, <2>2, EncodeVal
        <4>3. Tri[(y + 1) + 0] = Tri[y] + (y + 1)
          <5>1. (y + 1) + 0 = y + 1 BY <2>2
          <5>2. QED BY <5>1, <2>2, TriStep
        <4>4. n = Tri[y] + y BY <2>4, <3>1, <2>2
        <4>5. Tri[y] \in Nat /\ Tri[(y + 1) + 0] \in Nat BY <2>2, TriNat
        <4>6. QED BY <4>2, <4>3, <4>4, <4>5, <2>2, SMT
      <3>2. CASE x # 0
        <4>1. x \in Nat /\ x # 0 /\ y \in Nat BY <2>2, <3>2
        <4>2. Unpair[n+1] = <<x - 1, y + 1>> BY <2>5, <3>2
        <4>3. (x - 1) \in Nat /\ (y + 1) \in Nat /\ (x - 1) + (y + 1) = x + y BY <4>1
        <4>4. Encode[Unpair[n+1]] = Tri[(x - 1) + (y + 1)] + (y + 1) BY <4>2, <4>3, EncodeVal
        <4>5. Tri[(x - 1) + (y + 1)] = Tri[x + y] BY <4>3
        <4>6. Tri[x + y] \in Nat /\ Tri[(x - 1) + (y + 1)] \in Nat BY <4>1, <4>3, TriNat
        <4>7. QED BY <4>4, <4>5, <4>6, <2>4, <4>1, <2>2, SMT
      <3>3. QED BY <3>1, <3>2
    <2>7. QED BY <2>6 DEF P
  <1>3. \A n \in Nat : P(n)
    <2> HIDE DEF P
    <2> QED BY <1>1, <1>2, NatInduction, Isa
  <1>4. QED BY <1>3

(***************************************************************************)
(* Tri is (weakly) monotone:  a <= b  =>  Tri[a] <= Tri[b].              *)
(***************************************************************************)
THEOREM TriMonoLE == \A a \in Nat, b \in Nat : a <= b => Tri[a] <= Tri[b]
  <1> DEFINE Q(b) == \A a \in Nat : a <= b => Tri[a] <= Tri[b]
  <1>1. Q(0)
    <2> SUFFICES ASSUME NEW a \in Nat, a <= 0 PROVE Tri[a] <= Tri[0] BY DEF Q
    <2>1. a = 0 OBVIOUS
    <2>2. QED BY <2>1, TriNat
  <1>2. ASSUME NEW b \in Nat, Q(b) PROVE Q(b+1)
    <2> SUFFICES ASSUME NEW a \in Nat, a <= b + 1 PROVE Tri[a] <= Tri[b+1] BY DEF Q
    <2>1. Tri[b+1] = Tri[b] + (b + 1) BY TriStep
    <2>2. Tri[a] \in Nat /\ Tri[b] \in Nat /\ Tri[b+1] \in Nat BY TriNat
    <2>3. a <= b \/ a = b + 1 OBVIOUS
    <2>4. CASE a <= b
      <3>1. Tri[a] <= Tri[b] BY <1>2, <2>4 DEF Q
      <3>2. QED BY <3>1, <2>1, <2>2, SMT
    <2>5. CASE a = b + 1
      <3>1. QED BY <2>5, <2>2
    <2>6. QED BY <2>3, <2>4, <2>5
  <1>3. \A b \in Nat : Q(b)
    <2> HIDE DEF Q
    <2> QED BY <1>1, <1>2, NatInduction, Isa
  <1>4. QED BY <1>3

(***************************************************************************)
(* For p with diagonal d = p[1]+p[2]:   Tri[d] <= Encode[p] < Tri[d+1].   *)
(***************************************************************************)
THEOREM TriBounds ==
  \A p \in Pairs : /\ Tri[p[1] + p[2]] <= Encode[p]
                   /\ Encode[p] < Tri[p[1] + p[2] + 1]
  <1>1. TAKE p \in Pairs
  <1>2. p[1] \in Nat /\ p[2] \in Nat /\ p = <<p[1], p[2]>> BY DEF Pairs
  <1> DEFINE d == p[1] + p[2]
  <1>3. d \in Nat /\ p[2] <= d BY <1>2
  <1>4. Encode[p] = Tri[d] + p[2] BY <1>2, EncodeVal
  <1>5. Tri[d + 1] = Tri[d] + (d + 1) BY <1>3, TriStep
  <1>6. Tri[d] \in Nat /\ Tri[d + 1] \in Nat BY <1>3, TriNat
  <1>7. QED BY <1>2, <1>3, <1>4, <1>5, <1>6, SMT

(***************************************************************************)
(* Encode is injective.                                                    *)
(***************************************************************************)
THEOREM Injective == \A p \in Pairs, q \in Pairs : Encode[p] = Encode[q] => p = q
  <1>1. TAKE p \in Pairs, q \in Pairs
  <1>2. ASSUME Encode[p] = Encode[q] PROVE p = q
    <2>1. /\ p[1] \in Nat /\ p[2] \in Nat /\ p = <<p[1], p[2]>>
          /\ q[1] \in Nat /\ q[2] \in Nat /\ q = <<q[1], q[2]>>
      BY DEF Pairs
    <2> DEFINE dp == p[1] + p[2]
    <2> DEFINE dq == q[1] + q[2]
    <2>2. dp \in Nat /\ dq \in Nat BY <2>1
    <2>3. Encode[p] = Tri[dp] + p[2] /\ Encode[q] = Tri[dq] + q[2] BY <2>1, EncodeVal
    <2>3c. Encode[p] \in Nat /\ Encode[q] \in Nat BY <1>1, EncodeType
    <2>4. /\ Tri[dp] <= Encode[p] /\ Encode[p] < Tri[dp + 1]
          /\ Tri[dq] <= Encode[q] /\ Encode[q] < Tri[dq + 1]
      BY <1>1, TriBounds
    <2>5. (dp + 1 <= dq) => Tri[dp + 1] <= Tri[dq] BY <2>2, TriMonoLE
    <2>6. (dq + 1 <= dp) => Tri[dq + 1] <= Tri[dp] BY <2>2, TriMonoLE
    <2>7. /\ Tri[dp] \in Nat /\ Tri[dq] \in Nat
          /\ Tri[dp + 1] \in Nat /\ Tri[dq + 1] \in Nat
      BY <2>2, TriNat
    <2>8a. ~(dp + 1 <= dq) BY <1>2, <2>1, <2>3, <2>3c, <2>4, <2>5, <2>7, SMT
    <2>8b. ~(dq + 1 <= dp) BY <1>2, <2>1, <2>3, <2>3c, <2>4, <2>6, <2>7, SMT
    <2>8. dp = dq BY <2>2, <2>8a, <2>8b, SMT
    <2>9. p[2] = q[2] BY <1>2, <2>1, <2>2, <2>3, <2>7, <2>8, SMT
    <2>10. p[1] = q[1] BY <2>1, <2>2, <2>8, <2>9, SMT
    <2>11. QED BY <2>1, <2>9, <2>10
  <1>3. QED BY <1>2

(***************************************************************************)
(* Left inverse:  Unpair o Encode = identity on Pairs.                    *)
(* (Follows from the right inverse together with injectivity.)            *)
(***************************************************************************)
THEOREM UnpairEncode == \A p \in Pairs : Unpair[Encode[p]] = p
  <1>1. TAKE p \in Pairs
  <1>2. Encode[p] \in Nat BY <1>1, EncodeType
  <1>3. Unpair[Encode[p]] \in Pairs BY <1>2, UnpairType
  <1>4. Encode[Unpair[Encode[p]]] = Encode[p] BY <1>2, EncodeUnpair
  <1>5. QED BY <1>1, <1>3, <1>4, Injective

(***************************************************************************)
(* Encode is surjective.                                                   *)
(***************************************************************************)
THEOREM Surjective == \A n \in Nat : \E p \in Pairs : Encode[p] = n
  <1>1. TAKE n \in Nat
  <1>2. Unpair[n] \in Pairs BY <1>1, UnpairType
  <1>3. Encode[Unpair[n]] = n BY <1>1, EncodeUnpair
  <1>4. QED BY <1>2, <1>3

(***************************************************************************)
(* THE ISOMORPHISM.  Encode and Unpair are mutually inverse bijections    *)
(* between Pairs = Nat x Nat and Nat.                                      *)
(***************************************************************************)
THEOREM Isomorphism ==
  /\ Encode \in [Pairs -> Nat]
  /\ Unpair \in [Nat -> Pairs]
  /\ \A p \in Pairs : Unpair[Encode[p]] = p
  /\ \A n \in Nat   : Encode[Unpair[n]] = n
  BY EncodeType, UnpairType, UnpairEncode, EncodeUnpair

(* Stated with the standard library's Bijection operator. *)
THEOREM EncodeIsBijection == Encode \in Bijection(Pairs, Nat)
  <1>1. Encode \in [Pairs -> Nat] BY EncodeType
  <1>2. IsInjective(Encode) BY Injective, EncodeType DEF IsInjective
  <1>3. Encode \in Injection(Pairs, Nat) BY <1>1, <1>2 DEF Injection
  <1>4. Encode \in Surjection(Pairs, Nat) BY <1>1, Surjective DEF Surjection
  <1>5. QED BY <1>3, <1>4 DEF Bijection

(***************************************************************************)
(* THE ORDER PROPERTY.  Increasing either component of the pair strictly  *)
(* increases the natural number it is mapped to.                          *)
(***************************************************************************)
THEOREM MonotoneFirst == \A x \in Nat, y \in Nat : Encode[<<x + 1, y>>] > Encode[<<x, y>>]
  <1>1. TAKE x \in Nat, y \in Nat
  <1>2. x + y \in Nat OBVIOUS
  <1>3. Encode[<<x, y>>] = Tri[x + y] + y BY EncodeVal
  <1>4. Encode[<<x + 1, y>>] = Tri[(x + 1) + y] + y BY EncodeVal
  <1>5. (x + 1) + y = (x + y) + 1 OBVIOUS
  <1>6. Tri[(x + y) + 1] = Tri[x + y] + ((x + y) + 1) BY <1>2, TriStep
  <1>7. Tri[x + y] \in Nat BY <1>2, TriNat
  <1>8. QED BY <1>3, <1>4, <1>5, <1>6, <1>7, SMT

THEOREM MonotoneSecond == \A x \in Nat, y \in Nat : Encode[<<x, y + 1>>] > Encode[<<x, y>>]
  <1>1. TAKE x \in Nat, y \in Nat
  <1>2. x + y \in Nat OBVIOUS
  <1>3. Encode[<<x, y>>] = Tri[x + y] + y BY EncodeVal
  <1>4. Encode[<<x, y + 1>>] = Tri[x + (y + 1)] + (y + 1) BY EncodeVal
  <1>5. x + (y + 1) = (x + y) + 1 OBVIOUS
  <1>6. Tri[(x + y) + 1] = Tri[x + y] + ((x + y) + 1) BY <1>2, TriStep
  <1>7. Tri[x + y] \in Nat BY <1>2, TriNat
  <1>8. QED BY <1>3, <1>4, <1>5, <1>6, <1>7, SMT

(* The required property, both directions together. *)
THEOREM Monotone ==
  \A x \in Nat, y \in Nat :
     /\ Encode[<<x + 1, y>>] > Encode[<<x, y>>]
     /\ Encode[<<x, y + 1>>] > Encode[<<x, y>>]
  BY MonotoneFirst, MonotoneSecond

(***************************************************************************)
(* Tri dominates the identity:  Tri[d] >= d.                              *)
(***************************************************************************)
LEMMA TriGeId == \A d \in Nat : Tri[d] >= d
  <1> DEFINE P(d) == Tri[d] >= d
  <1>1. P(0) BY Tri0
  <1>2. ASSUME NEW d \in Nat, P(d) PROVE P(d+1)
    <2>1. Tri[d+1] = Tri[d] + (d + 1) BY TriStep
    <2>2. Tri[d] \in Nat BY TriNat
    <2>3. QED BY <2>1, <2>2, SMT DEF P
  <1>3. \A d \in Nat : P(d)
    <2> HIDE DEF P
    <2> QED BY <1>1, <1>2, NatInduction, Isa
  <1>4. QED BY <1>3

(***************************************************************************)
(* Increasing the FIRST component past its own value: for y > 0, encoding *)
(* <<a, y>> always yields a strictly larger number than a itself.         *)
(***************************************************************************)
LEMMA EncodeFirstGrows == \A a \in Nat, y \in Nat : y > 0 => Encode[<<a, y>>] > a
  <1>1. TAKE a \in Nat, y \in Nat
  <1>2. a + y \in Nat OBVIOUS
  <1>3. Encode[<<a, y>>] = Tri[a + y] + y BY EncodeVal
  <1>4. Tri[a + y] >= a + y BY <1>2, TriGeId
  <1>5. Tri[a + y] \in Nat BY <1>2, TriNat
  <1>6. QED BY <1>3, <1>4, <1>5, SMT

(***************************************************************************)
(* Tri STRICTLY dominates the identity once the argument is >= 2:         *)
(* Tri[d] > d for d >= 2.  (Tri[d] = Tri[d-1] + d and Tri[d-1] >= 1.)     *)
(***************************************************************************)
LEMMA TriGtId == \A d \in Nat : d >= 2 => Tri[d] > d
  <1>1. TAKE d \in Nat
  <1>2. CASE d >= 2
    <2>1. d - 1 \in Nat /\ (d - 1) + 1 = d /\ d - 1 >= 1 BY <1>2, SMT
    <2>2. Tri[(d - 1) + 1] = Tri[d - 1] + ((d - 1) + 1) BY <2>1, TriStep
    <2>3. Tri[d - 1] >= d - 1 BY <2>1, TriGeId
    <2>4. Tri[d - 1] \in Nat BY <2>1, TriNat
    <2>5. QED BY <1>2, <2>1, <2>2, <2>3, <2>4, SMT
  <1>3. CASE ~(d >= 2)
    <2>1. QED BY <1>3, SMT
  <1>4. QED BY <1>2, <1>3

(***************************************************************************)
(* Encoding the pair <<Encode[<<x,y>>], y>> strictly exceeds             *)
(* Encode[<<x,y>>] whenever y > 0 OR x > 1.                               *)
(*   - If y > 0, this is EncodeFirstGrows at a := Encode[<<x,y>>].        *)
(*   - If y = 0 and x > 1, then Encode[<<x,0>>] = Tri[x] >= x >= 2, so    *)
(*     re-encoding gives Tri[Tri[x]] > Tri[x] by TriGtId.                 *)
(***************************************************************************)
THEOREM EncodingGreater == \A x \in Nat, y \in Nat : y > 0 \/ x > 1 =>
  Encode[<<Encode[<<x,y>>], y>>] > Encode[<<x,y>>]
  <1>1. TAKE x \in Nat, y \in Nat
  <1>2. <<x, y>> \in Pairs BY DEF Pairs
  <1>3. Encode[<<x,y>>] \in Nat BY <1>2, EncodeType
  <1>4. CASE y > 0
    <2>1. Encode[<<Encode[<<x,y>>], y>>] > Encode[<<x,y>>]
      BY <1>3, <1>4, EncodeFirstGrows
    <2>2. QED BY <2>1
  <1>5. CASE ~(y > 0)
    <2>1. y = 0 BY <1>5, SMT
    <2>2. CASE x > 1
      <3>0. x + y = x BY <2>1, SMT
      <3>1. Encode[<<x, y>>] = Tri[x]
        <4>1. Encode[<<x, y>>] = Tri[x + y] + y BY EncodeVal
        <4>2. Tri[x + y] = Tri[x] BY <3>0
        <4>3. Tri[x] \in Nat BY TriNat
        <4>4. QED BY <4>1, <4>2, <4>3, <2>1, SMT
      <3>2. Tri[x] >= x BY TriGeId
      <3>3. Encode[<<x,y>>] >= 2 BY <1>3, <2>2, <3>1, <3>2, SMT
      <3>4. Encode[<<x,y>>] + y = Encode[<<x,y>>] BY <2>1, <1>3, SMT
      <3>5. Encode[<<Encode[<<x,y>>], y>>] = Tri[Encode[<<x,y>>]]
        <4>1. Encode[<<Encode[<<x,y>>], y>>] = Tri[Encode[<<x,y>>] + y] + y
          BY <1>3, EncodeVal
        <4>2. Tri[Encode[<<x,y>>] + y] = Tri[Encode[<<x,y>>]] BY <3>4
        <4>3. Tri[Encode[<<x,y>>]] \in Nat BY <1>3, TriNat
        <4>4. QED BY <4>1, <4>2, <4>3, <2>1, SMT
      <3>6. Tri[Encode[<<x,y>>]] > Encode[<<x,y>>] BY <1>3, <3>3, TriGtId
      <3>7. QED BY <3>5, <3>6, SMT
    <2>3. CASE ~(x > 1)
      <3>1. QED BY <1>5, <2>3, SMT
    <2>4. QED BY <2>2, <2>3
  <1>6. QED BY <1>4, <1>5

================================================================================
