------------------------------ MODULE MemoPFields ------------------------------
\* Member-level agreement: a message whose MemoP record is good stores the
\* same READABLE data as its canonical Memo.  Every field an assembly ever
\* reads off a member record is covered: id, bal, newbal, caught, lrns, the
\* frontier maps (domain and pointwise -- the maps are only ever read at a
\* learner, never compared as records) and highesttwoas in projection
\* (domain, and each entry's ballot).
\*
\* The fields deliberately NOT here are fresh, isoneb, deepestknown and
\* prevtran: no assembly reads fresh or isoneb off a member, and
\* deepestknown / prevtran genuinely differ -- the P-side entries are
\* MemoP records and the CHOOSE tie-breaks need not agree.  The two
\* value-determined comparisons (frontier depth, entry ballot) go through
\* attainment-plus-maximality on both sides, not through the records.
EXTENDS MemoPDefs, BalRec, NewBalRec, CaughtRec, LrnsRec, MaxQDepthInv,
        HighestTwoAsRec, BBallot, TranSubMessages
LOCAL INSTANCE TLAPS

LEMMA MemoPFields ==
  ASSUME MessageInterfaceAssumptions,
         LearnersMightAgree, ValidLearnerGraphAssumption,
         NEW m \in Messages, MemoPGood(m)
  PROVE /\ MemoP(m).id = m
        /\ MemoP(m).bal = Memo(m).bal
        /\ (MemoP(m).newbal <=> Memo(m).newbal)
        /\ MemoP(m).caught = Memo(m).caught
        /\ MemoP(m).lrns = Memo(m).lrns
        /\ DOMAIN MemoP(m).maxqdepth = DOMAIN Memo(m).maxqdepth
        /\ \A alpha \in DOMAIN MemoP(m).maxqdepth :
             /\ MemoP(m).maxqdepth[alpha] = Memo(m).maxqdepth[alpha]
             /\ MemoP(m).pendingqd[alpha] = Memo(m).pendingqd[alpha]
        /\ DOMAIN MemoP(m).highesttwoas = DOMAIN Memo(m).highesttwoas
        /\ \A l \in DOMAIN MemoP(m).highesttwoas :
             MemoP(m).highesttwoas[l].bal = Memo(m).highesttwoas[l].bal
<1>tok. TypeOKMessageInterface  BY DEF MessageInterfaceAssumptions
<1>tf. TranFinite  BY DEF MessageInterfaceAssumptions
<1>tt. TranTrans  BY DEF MessageInterfaceAssumptions
<1>ta. TranAcyclic  BY DEF MessageInterfaceAssumptions
<1>anp. AlwaysAProposal  BY DEF MessageInterfaceAssumptions
<1>teM. TranExclusive(m) \subseteq Messages
  BY <1>tok, TranSubMessages DEF TranExclusive
\* ----------------------------------------------------- value-determined fields
<1>id. MemoP(m).id = m  BY DEF MemoPGood
<1>bal. MemoP(m).bal = Memo(m).bal
  <2>1. MemoP(m).bal = B(m)  BY DEF MemoPGood
  <2>2. MemoBal(m) = B(m)
    BY <1>tok, <1>tt, <1>tf, <1>ta, <1>anp, BalRec
  <2> QED BY <2>1, <2>2 DEF MemoBal
<1>nb. MemoP(m).newbal <=> Memo(m).newbal
  <2>1. MemoP(m).newbal <=> (\A y \in Refs(m) : B(y) < B(m))
    BY DEF MemoPGood
  <2>2. MemoNewBal(m) <=> (\A y \in Refs(m) : B(y) < B(m))
    BY <1>tok, <1>tt, <1>tf, <1>ta, <1>anp, NewBalRec
  <2> QED BY <2>1, <2>2 DEF MemoNewBal
<1>ca. MemoP(m).caught = Memo(m).caught
  <2>1. MemoP(m).caught = Caught(m)  BY DEF MemoPGood
  <2>2. MemoCaught(m) = Caught(m)
    BY <1>tok, <1>tt, <1>tf, <1>ta, CaughtRec
  <2> QED BY <2>1, <2>2 DEF MemoCaught
<1>lr. MemoP(m).lrns = Memo(m).lrns
  <2>1. MemoP(m).lrns = Lrns(m)  BY DEF MemoPGood
  <2>2. MemoLrns(m) = Lrns(m)  BY LrnsRec
  <2> QED BY <2>1, <2>2 DEF MemoLrns
\* ------------------------------------------------------------- frontier maps
<1>mqP. MaxQDepthCorrect(m, MemoP(m).maxqdepth, MemoP(m).pendingqd)
  BY DEF MemoPGood
<1>mqC. MaxQDepthCorrect(m, Memo(m).maxqdepth, Memo(m).pendingqd)
  <2>1. MaxQDepthInvariant(m)  BY MaxQDepthInv
  <2> QED BY <2>1
    DEF MaxQDepthInvariant, MaxQDepthCorrect, MemoMaxQDepth, MemoPendingQd
<1>mqdom. DOMAIN MemoP(m).maxqdepth = DOMAIN Memo(m).maxqdepth
  BY <1>mqP, <1>mqC DEF MaxQDepthCorrect
<1>mqval. \A alpha \in DOMAIN MemoP(m).maxqdepth :
            /\ MemoP(m).maxqdepth[alpha] = Memo(m).maxqdepth[alpha]
            /\ MemoP(m).pendingqd[alpha] = Memo(m).pendingqd[alpha]
  <2> SUFFICES ASSUME NEW alpha \in DOMAIN MemoP(m).maxqdepth
      PROVE /\ MemoP(m).maxqdepth[alpha] = Memo(m).maxqdepth[alpha]
            /\ MemoP(m).pendingqd[alpha] = Memo(m).pendingqd[alpha]
    OBVIOUS
  <2>aC. alpha \in DOMAIN Memo(m).maxqdepth  BY <1>mqdom
  <2>pf. /\ MemoP(m).maxqdepth[alpha] \in Nat
         /\ \E y \in Tran(m) :
              B(y) = B(m) /\ HasDepth(alpha, y, MemoP(m).maxqdepth[alpha])
         /\ \A y \in Tran(m) : \A d \in Nat :
              (B(y) = B(m) /\ HasDepth(alpha, y, d))
                => d <= MemoP(m).maxqdepth[alpha]
         /\ MemoP(m).pendingqd[alpha]
              = {y \in Tran(m) :
                   /\ B(y) = B(m)
                   /\ HasDepth(alpha, y, MemoP(m).maxqdepth[alpha])}
    BY <1>mqP DEF MaxQDepthCorrect
  <2>cf. /\ Memo(m).maxqdepth[alpha] \in Nat
         /\ \E y \in Tran(m) :
              B(y) = B(m) /\ HasDepth(alpha, y, Memo(m).maxqdepth[alpha])
         /\ \A y \in Tran(m) : \A d \in Nat :
              (B(y) = B(m) /\ HasDepth(alpha, y, d))
                => d <= Memo(m).maxqdepth[alpha]
         /\ Memo(m).pendingqd[alpha]
              = {y \in Tran(m) :
                   /\ B(y) = B(m)
                   /\ HasDepth(alpha, y, Memo(m).maxqdepth[alpha])}
    BY <1>mqC, <2>aC DEF MaxQDepthCorrect
  <2>le1. MemoP(m).maxqdepth[alpha] <= Memo(m).maxqdepth[alpha]
    <3>1. PICK y \in Tran(m) :
            B(y) = B(m) /\ HasDepth(alpha, y, MemoP(m).maxqdepth[alpha])
      BY <2>pf
    <3> QED BY <3>1, <2>pf, <2>cf
  <2>le2. Memo(m).maxqdepth[alpha] <= MemoP(m).maxqdepth[alpha]
    <3>1. PICK y \in Tran(m) :
            B(y) = B(m) /\ HasDepth(alpha, y, Memo(m).maxqdepth[alpha])
      BY <2>cf
    <3> QED BY <3>1, <2>pf, <2>cf
  <2>eq. MemoP(m).maxqdepth[alpha] = Memo(m).maxqdepth[alpha]
    BY <2>le1, <2>le2, <2>pf, <2>cf, SMT
  <2> QED BY <2>eq, <2>pf, <2>cf
\* -------------------------------------------------------- highesttwoas, in bal
<1>htP. /\ DOMAIN MemoP(m).highesttwoas
             = {l \in Learners : \E y \in TranExclusive(m) : l \in Lrns(y)}
        /\ \A l \in DOMAIN MemoP(m).highesttwoas :
             /\ \E y \in TranExclusive(m) :
                  l \in Lrns(y) /\ B(y) = MemoP(m).highesttwoas[l].bal
             /\ \A y \in TranExclusive(m) :
                  l \in Lrns(y) => B(y) <= MemoP(m).highesttwoas[l].bal
  BY DEF MemoPGood
<1>htC. HighestTwoAsInvariant(m)  BY HighestTwoAsRec
<1>htdom. DOMAIN MemoP(m).highesttwoas = DOMAIN Memo(m).highesttwoas
  BY <1>htP, <1>htC DEF HighestTwoAsInvariant, MemoHighestTwoAs
<1>htbal. \A l \in DOMAIN MemoP(m).highesttwoas :
            MemoP(m).highesttwoas[l].bal = Memo(m).highesttwoas[l].bal
  <2> SUFFICES ASSUME NEW l \in DOMAIN MemoP(m).highesttwoas
      PROVE MemoP(m).highesttwoas[l].bal = Memo(m).highesttwoas[l].bal
    OBVIOUS
  <2>lC. l \in DOMAIN MemoHighestTwoAs(m)
    BY <1>htdom DEF MemoHighestTwoAs
  <2>cf. /\ MemoHighestTwoAs(m)[l] = Memo(MemoHighestTwoAs(m)[l].id)
         /\ MemoHighestTwoAs(m)[l].id \in TranExclusive(m)
         /\ l \in Lrns(MemoHighestTwoAs(m)[l].id)
         /\ \A y \in TranExclusive(m) :
              l \in Lrns(y) => B(y) <= B(MemoHighestTwoAs(m)[l].id)
    BY <1>htC, <2>lC DEF HighestTwoAsInvariant
  <2>cid. MemoHighestTwoAs(m)[l].id \in Messages  BY <2>cf, <1>teM
  <2>cbal. Memo(m).highesttwoas[l].bal = B(MemoHighestTwoAs(m)[l].id)
    <3>1. MemoBal(MemoHighestTwoAs(m)[l].id) = B(MemoHighestTwoAs(m)[l].id)
      BY <2>cid, <1>tok, <1>tt, <1>tf, <1>ta, <1>anp, BalRec
    <3> QED BY <2>cf, <3>1 DEF MemoBal, MemoHighestTwoAs
  <2>pw. PICK y \in TranExclusive(m) :
           l \in Lrns(y) /\ B(y) = MemoP(m).highesttwoas[l].bal
    BY <1>htP
  <2>le1. MemoP(m).highesttwoas[l].bal <= B(MemoHighestTwoAs(m)[l].id)
    BY <2>pw, <2>cf
  <2>le2. B(MemoHighestTwoAs(m)[l].id) <= MemoP(m).highesttwoas[l].bal
    BY <2>cf, <1>htP
  <2>nat1. MemoP(m).highesttwoas[l].bal \in Nat
    <3>1. y \in Messages  BY <2>pw, <1>teM
    <3>2. B(y) \in Ballots  BY <3>1, <1>tok, <1>tf, <1>anp, BBallot
    <3> QED BY <2>pw, <3>2 DEF Ballots
  <2>nat2. B(MemoHighestTwoAs(m)[l].id) \in Nat
    <3>1. B(MemoHighestTwoAs(m)[l].id) \in Ballots
      BY <2>cid, <1>tok, <1>tf, <1>anp, BBallot
    <3> QED BY <3>1 DEF Ballots
  <2> QED BY <2>le1, <2>le2, <2>nat1, <2>nat2, <2>cbal, SMT
<1> QED BY <1>id, <1>bal, <1>nb, <1>ca, <1>lr, <1>mqdom, <1>mqval,
             <1>htdom, <1>htbal
=============================================================================
