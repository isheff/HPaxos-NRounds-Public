------------------------------ MODULE BalRec ------------------------------
\*   BalStep, MemoRec, RefsInduction -> cited lemmas
\*   TLAPS -> proof-only
EXTENDS RecursiveWellFormed, BalStep, MemoRec, RefsInduction
LOCAL INSTANCE TLAPS

\* Induction motive, module-level so RefsInduction can instantiate it by
\* name.
BalRecP(z) == MemoBal(z) = B(z)

\* The recursively-assembled bal field is exactly B: instantiate the
\* generalized step at S := Refs(m) and identify the assembly with the
\* stored field.
LEMMA BalRec ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         AlwaysAProposal,
         NEW m \in Messages
  PROVE MemoBal(m) = B(m)
<1>cl. \A x \in Messages : (\A y \in Refs(x) : BalRecP(y)) => BalRecP(x)
  <2> SUFFICES ASSUME NEW x \in Messages,
                      \A y \in Refs(x) : BalRecP(y)
      PROVE BalRecP(x)
    OBVIOUS
  <2>1. Refs(x) \subseteq TranExclusive(x)  BY DEF Refs
  <2>2. \A p \in Refs(x) : MemoBal(p) = B(p)  BY DEF BalRecP
  <2>3. BalAssemble(x, {Memo(p) : p \in Refs(x)}) = B(x)
    BY <2>1, <2>2, BalStep
  <2>4. Memo(x) = MemoR(x, {Memo(p) : p \in Refs(x)})  BY MemoRec
  <2>5. MemoBal(x) = BalAssemble(x, {Memo(p) : p \in Refs(x)})
    BY <2>4 DEF MemoBal, MemoR
  <2> QED BY <2>3, <2>5 DEF BalRecP
<1>1. BalRecP(m)  BY <1>cl, RefsInduction
<1> QED BY <1>1 DEF BalRecP
====================================================================
