--------------------------- MODULE WellFormedRecDef ---------------------------
\* Definitions only; the equivalence theorem is CWellFormedRec.
\*
\* WellFormedRec: the memo-based well-formedness check an acceptor runs
\* on a RECEIVED CANDIDATE record cand = [sender, payload, priors], given
\* only the DIGESTS of its priors (all already-accepted messages). Every
\* conjunct reads the priors' memos alone -- no use of Tran or CTran
\* anywhere -- so checking cost scales with |priors| x |Learners/signers|,
\* never with |Tran|.  (Priors-canonicality, m.priors = CRefs(m), is NOT
\* checked: it is provably not decidable from bounded memos when a
\* prior's signer has equivocated.  It is not part of CWellFormed either;
\* it holds for safe acceptors' own sends as an algorithm invariant --
\* CSafeSentCanonical.)
\*
\* The WFR* operators are the candidate-record variants of the memo
\* assembly operators: identical bodies with the interface macros on the
\* (possibly not-yet-well-formed) candidate replaced by its record fields
\* (sender for Sig, payload \in CProposal for IsProposal, payload.ballot
\* for ProposalBal). CaughtAssemble needs no variant: it never looks at
\* the assembling message itself.
EXTENDS MessageConcrete, RecursiveWellFormed

\* The IMPLEMENTATION's memo: recursively assembled over the PRIORS field --
\* what an acceptor actually stores, since it never computes Refs (that
\* would need Tran).  Memo (refs-recursive) and MemoP agree on every
\* value-determined field (MemoPGoodInv / MemoPFields); they may differ in
\* the CHOOSE-tie-broken witnesses inside deepestknown / highesttwoas /
\* prevtran when a prior set is non-canonical, which no check outcome
\* depends on.
MemoP(x) == CRecursiveFunc(MemoR, CPriors, x)

\* Ballot of the candidate: max of priors' ballots plus its own proposal
\* ballot (mirrors BalAssemble).
WFRBal(pl, r) ==
  Max({rc.bal : rc \in r}
      \cup (IF pl \in CProposal THEN {pl.ballot} ELSE {}))

\* Mirrors NewBalAssemble.
WFRNewBal(pl, r) == \A rc \in r : rc.bal < WFRBal(pl, r)

\* Mirrors IsOneBAssemble: a same-ballot proposal prior with newbal, all
\* other priors strictly lower.
WFRIsOneB(pl, r) ==
  /\ pl \notin CProposal
  /\ \E rc \in r :
       /\ CIsProposal(rc.id)
       /\ rc.bal = WFRBal(pl, r)
       /\ rc.newbal
       /\ \A rc2 \in r : rc2 = rc \/ rc2.bal < WFRBal(pl, r)

\* Mirrors SBRefs/QDepthCands/QDom/RefFrontier/RefPending/Bump for the
\* candidate's ballot.
WFRSBRefs(pl, r) == {rc \in r : rc.bal = WFRBal(pl, r)}

WFRQDepthCands(alpha, pl, r) ==
  {QDepthCand(alpha, rc) :
     rc \in {y \in WFRSBRefs(pl, r) : alpha \in DOMAIN y.maxqdepth}}

WFRQDom(pl, r) == {alpha \in Learners :
                     \E rc \in WFRSBRefs(pl, r) : alpha \in DOMAIN rc.maxqdepth}

WFRRefFrontier(alpha, pl, r) == Max(WFRQDepthCands(alpha, pl, r))

WFRRefPending(alpha, pl, r) ==
  UNION {RefPendingPart(alpha, rc) :
           rc \in {y \in WFRSBRefs(pl, r) :
                     /\ alpha \in DOMAIN y.maxqdepth
                     /\ y.maxqdepth[alpha] = WFRRefFrontier(alpha, pl, r)}}

WFRBump(alpha, sdr, pl, r) ==
  /\ sdr \in Acceptors
  /\ CSigS(WFRRefPending(alpha, pl, r)) \in Quorums(alpha)

\* Mirrors FreshAssemble, against the candidate's ballot.
WFRFresh(alpha, pl, r) ==
  \A l \in ConFromCaught(alpha, CaughtAssemble(r))
             \cap DOMAIN HighestTwoAsAssemble(r) :
    \/ BalToVal(HighestTwoAsAssemble(r)[l].bal) = BalToVal(WFRBal(pl, r))
    \/ \E l2 \in ConFromCaught(alpha, CaughtAssemble(r))
                   \cap DOMAIN HighestTwoAsAssemble(r) :
         HighestTwoAsAssemble(r)[l2].bal > HighestTwoAsAssemble(r)[l].bal

\* Mirrors LrnsAssemble: the learners the CANDIDATE itself would attest
\* depth 1 for. (Frontier >= 1: inherited quorum needs only acceptor-
\* signedness; frontier 0: the pending level-0 attesters must form a
\* quorum -- but a OneB candidate is itself only a LEVEL-0 attester, so
\* depth 1 of the candidate needs the quorum among its PRIORS' history.)
WFRLrns(sdr, pl, r) ==
  {alpha \in WFRQDom(pl, r) :
     IF WFRRefFrontier(alpha, pl, r) >= 1
       THEN sdr \in Acceptors
       ELSE WFRBump(alpha, sdr, pl, r)}

\* Mirrors IsTwoAMemo's characterization.
WFRIsTwoA(sdr, pl, r) == pl \notin CProposal /\ WFRLrns(sdr, pl, r) # {}

\* The memo-based candidate check, equivalent (CWellFormedRec, under
\* MessageInterface = CMI with priors \subseteq CMessages) to
\* CWellFormed(cand):
\*   1. a proposal exists in the closure: the candidate is one, or it has
\*      a prior (every well-formed prior carries one, by AlwaysAProposal);
\*   2. an acceptor may not catch itself: caught is assembled from the
\*      priors' memos (the candidate can never be half of a fork with
\*      its own ancestor);
\*   3. proposal / OneB / TwoA, via the memo characterizations;
\*   4. a proposal's ballot field is its B (CFilterOut's clause).
WellFormedRec(cand) ==
  LET r == {Memo(p) : p \in cand.priors}
  IN  /\ CIsProposal(cand) \/ cand.priors # {}
      /\ cand.sender \in Acceptors => cand.sender \notin CaughtAssemble(r)
      /\ \/ CIsProposal(cand)
         \/ WFRIsOneB(cand.payload, r)
         \/ WFRIsTwoA(cand.sender, cand.payload, r)
      /\ CIsProposal(cand) => WFRBal(cand.payload, r) = cand.payload.ballot
====================================================================
