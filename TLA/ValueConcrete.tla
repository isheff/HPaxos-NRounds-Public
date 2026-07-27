--------------------------- MODULE ValueConcrete ---------------------------
\* CantorPairing MUST be EXTENDS, not LOCAL INSTANCE. `Unpair` appears inside the
\* body of the EXPORTED definition ValueInterfaceEx below, and every lemma module
\* in this split unfolds `DEF ValueInterfaceEx`. Under LOCAL INSTANCE each of
\* those modules would get its own private copy and see `Unpair_1`, which its own
\* CantorPairing facts cannot talk about. EXTENDS shares one copy; INSTANCE copies.
\* ValueInterface likewise supplies Ballots, which is in that same exported body.
\* Nothing else is needed here: Nat arrives transitively (CantorPairing EXTENDS
\* NaturalsInduction/Functions, both of which EXTENDS Integers), and TLAPS is not
\* referenced by any definition -- the lemma modules take it themselves.
EXTENDS ValueInterface, CantorPairing

CONSTANT ValuesEx
\* defining the main example
ValuesExAssumption == ValuesEx # {} /\ ValuesEx \subseteq Nat
DefaultValue == CHOOSE x \in ValuesEx : TRUE
ValueInterfaceEx == [
  values   |-> ValuesEx,
  baltoval |-> [x \in Ballots |->
    IF Unpair[x][2] \in ValuesEx
    THEN Unpair[x][2]
    ELSE DefaultValue]]
====================================================================
