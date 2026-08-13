----------------------------- MODULE MemoPBalStep -----------------------------
\* MemoP tower, leg S1: the bal and newbal assemblies over the priors' MemoP
\* records are correct.  Pattern for every value-determined leg: the P-side
\* assembly reads only member projections that the induction hypothesis pins
\* to their semantic values, so it EQUALS the assembly over the priors'
\* canonical Memos -- and that one is handled by the S-generalized Cover
\* corollaries at S := priors (CRefsSubPriors supplies the sandwich).
EXTENDS MemoPDefs, CRefsSubPriors, BalCover, NewBalAssembleCover, BalRec,
        CFields, CMessageTranClosed, CTranResolve
LOCAL INSTANCE TLAPS

LEMMA MemoPBalStep ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         AlwaysAProposal, MessageInterface = CMI,
         NEW x \in CMessages,
         \A y \in CTranExcl(x) : MemoPGood(y)
  PROVE /\ BalAssemble(x, {MemoP(q) : q \in x.priors}) = B(x)
        /\ (NewBalAssemble(x, {MemoP(q) : q \in x.priors})
              <=> (\A y \in Refs(x) : B(y) < B(x)))
<1> DEFINE pr == x.priors
<1> DEFINE rP == {MemoP(q) : q \in pr}
<1> DEFINE rC == {Memo(q) : q \in pr}
<1>xm. x \in Messages  BY CFields
<1>sand. Refs(x) \subseteq pr /\ pr \subseteq TranExclusive(x)
  BY CRefsSubPriors
<1>teq. TranExclusive(x) = CTranExcl(x)
  <2>1. Tran(x) = CTran(x)  BY CTranResolve
  <2> QED BY <2>1 DEF TranExclusive, CTranExcl
<1>prM. pr \subseteq CMessages
  <2> SUFFICES ASSUME NEW q \in pr PROVE q \in CMessages  OBVIOUS
  <2>1. q \in CTranExcl(x)  BY <1>sand, <1>teq
  <2>2. q \in CTran(x)  BY <2>1 DEF CTranExcl
  <2> QED BY <2>2, CMessageTranClosed
<1>ihq. \A q \in pr : MemoPGood(q)
  BY <1>sand, <1>teq
<1>bals. \A q \in pr : MemoP(q).bal = B(q) /\ Memo(q).bal = B(q)
  <2> SUFFICES ASSUME NEW q \in pr
      PROVE MemoP(q).bal = B(q) /\ Memo(q).bal = B(q)  OBVIOUS
  <2>1. MemoP(q).bal = B(q)  BY <1>ihq DEF MemoPGood
  <2>2. q \in Messages  BY <1>prM, CFields
  <2>3. MemoBal(q) = B(q)  BY <2>2, BalRec
  <2> QED BY <2>1, <2>3 DEF MemoBal
<1>img. {rc.bal : rc \in rP} = {rc.bal : rc \in rC}
  <2>sub. {rc.bal : rc \in rP} \subseteq {rc.bal : rc \in rC}
    <3> SUFFICES ASSUME NEW rc \in rP
        PROVE rc.bal \in {rc2.bal : rc2 \in rC}  OBVIOUS
    <3>1. PICK q \in pr : rc = MemoP(q)  OBVIOUS
    <3>2. Memo(q) \in rC  OBVIOUS
    <3> QED BY <3>1, <3>2, <1>bals
  <2>sup. {rc.bal : rc \in rC} \subseteq {rc.bal : rc \in rP}
    <3> SUFFICES ASSUME NEW rc \in rC
        PROVE rc.bal \in {rc2.bal : rc2 \in rP}  OBVIOUS
    <3>1. PICK q \in pr : rc = Memo(q)  OBVIOUS
    <3>2. MemoP(q) \in rP  OBVIOUS
    <3> QED BY <3>1, <3>2, <1>bals
  <2> QED BY <2>sub, <2>sup
<1>baleq. BalAssemble(x, rP) = BalAssemble(x, rC)
  BY <1>img DEF BalAssemble
<1>balc. BalAssemble(x, rC) = B(x)
  BY <1>xm, <1>sand, BalCover
<1>c1. BalAssemble(x, rP) = B(x)
  BY <1>baleq, <1>balc
<1>nbc. NewBalAssemble(x, rC) <=> (\A y \in Refs(x) : B(y) < B(x))
  BY <1>xm, <1>sand, NewBalAssembleCover
<1>nbeq. NewBalAssemble(x, rP) <=> NewBalAssemble(x, rC)
  <2>1. NewBalAssemble(x, rP) <=> (\A rc \in rP : rc.bal < BalAssemble(x, rP))
    BY DEF NewBalAssemble
  <2>2. NewBalAssemble(x, rC) <=> (\A rc \in rC : rc.bal < BalAssemble(x, rC))
    BY DEF NewBalAssemble
  <2>3. (\A rc \in rP : rc.bal < BalAssemble(x, rP))
          <=> (\A rc \in rC : rc.bal < BalAssemble(x, rC))
    <3>f. (\A rc \in rP : rc.bal < BalAssemble(x, rP))
            => (\A rc \in rC : rc.bal < BalAssemble(x, rC))
      <4> SUFFICES ASSUME \A rc \in rP : rc.bal < BalAssemble(x, rP),
                          NEW rc \in rC
          PROVE rc.bal < BalAssemble(x, rC)  OBVIOUS
      <4>1. rc.bal \in {rc2.bal : rc2 \in rP}  BY <1>img
      <4>2. PICK rc2 \in rP : rc.bal = rc2.bal  BY <4>1
      <4> QED BY <4>2, <1>baleq
    <3>b. (\A rc \in rC : rc.bal < BalAssemble(x, rC))
            => (\A rc \in rP : rc.bal < BalAssemble(x, rP))
      <4> SUFFICES ASSUME \A rc \in rC : rc.bal < BalAssemble(x, rC),
                          NEW rc \in rP
          PROVE rc.bal < BalAssemble(x, rP)  OBVIOUS
      <4>1. rc.bal \in {rc2.bal : rc2 \in rC}  BY <1>img
      <4>2. PICK rc2 \in rC : rc.bal = rc2.bal  BY <4>1
      <4> QED BY <4>2, <1>baleq
    <3> QED BY <3>f, <3>b
  <2> QED BY <2>1, <2>2, <2>3
<1>c2. NewBalAssemble(x, rP) <=> (\A y \in Refs(x) : B(y) < B(x))
  BY <1>nbeq, <1>nbc
<1> QED BY <1>c1, <1>c2
=============================================================================
