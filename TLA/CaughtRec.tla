----------------------------- MODULE CaughtRec -----------------------------
\*   CaughtStep, MemoRec, RefsInduction -> cited lemmas
\*   TLAPS -> proof-only
EXTENDS RecursiveWellFormed, CaughtStep, MemoRec, RefsInduction
LOCAL INSTANCE TLAPS

\* Induction motive, module-level so RefsInduction can instantiate it by
\* name.
CaughtRecP(z) == MemoCaught(z) = Caught(z)

\* The recursively-assembled caught field is exactly Caught: instantiate
\* the generalized step at S := Refs(m) and identify the assembly with the
\* stored field.
LEMMA CaughtRec ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         NEW m \in Messages
  PROVE MemoCaught(m) = Caught(m)
<1>cl. \A x \in Messages : (\A y \in Refs(x) : CaughtRecP(y)) => CaughtRecP(x)
  <2> SUFFICES ASSUME NEW x \in Messages,
                      \A y \in Refs(x) : CaughtRecP(y)
      PROVE CaughtRecP(x)
    OBVIOUS
  <2>1. Refs(x) \subseteq TranExclusive(x)  BY DEF Refs
  <2>2. \A p \in Refs(x) : MemoCaught(p) = Caught(p)  BY DEF CaughtRecP
  <2>3. CaughtAssemble({Memo(p) : p \in Refs(x)}) = Caught(x)
    BY <2>1, <2>2, CaughtStep
  <2>4. Memo(x) = MemoR(x, {Memo(p) : p \in Refs(x)})  BY MemoRec
  <2>5. MemoCaught(x) = CaughtAssemble({Memo(p) : p \in Refs(x)})
    BY <2>4 DEF MemoCaught, MemoR
  <2> QED BY <2>3, <2>5 DEF CaughtRecP
<1>1. CaughtRecP(m)  BY <1>cl, RefsInduction
<1> QED BY <1>1 DEF CaughtRecP
====================================================================
