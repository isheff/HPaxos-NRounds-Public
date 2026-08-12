----------------------- MODULE RecursiveWellFormed -----------------------
\* Definitions only; lemmas live in their own modules.
\*
\* A DIGEST is the data structure our recursive function builds for each
\* message: a record summarizing the message's exclusive transitive history
\* compactly enough that the digest of x can be assembled from the digests
\* of Refs(x) alone -- the per-round assembly cost scales with |Refs(x)| and
\* the number of signers, NOT with |Tran(x)| (contrast CombinedFreshQdLrnsId,
\* which recurses over all of TranExclusive). Digest(x) is defined via
\* RecursiveMessageRefsFunc; DigestR is the assembly step, whose r argument
\* is the set of refs' digests.
\*
\* Digest fields so far:
\*   id           : the message itself (identifies whose digest each element
\*                  of r is during assembly)
\*   deepestknown : a function whose domain is (proven, in DeepestKnownInv,
\*                  equal to) SigS(TranExclusive(x)), mapping each signer s
\*                  of any message in TranExclusive(x) to a pair
\*                  <<n, d>> where n \in Nat and d is the DIGEST of a
\*                  message d.id \in TranExclusive(x) with Sig(d.id) = s,
\*                  such that:
\*                    - n = 0  iff  s \notin SigS(TranExclusive(d.id));
\*                    - n > 0  =>  s \in DOMAIN DeepestKnown(d.id) and
\*                      DeepestKnown(d.id)[s][1] = n - 1.
\*                  So <<n, d>> tracks a "deepest" message from s: one with
\*                  the longest chain of same-signer deepestknown-parents.
\*                  (Both facts follow from DeepestKnownInvariant below,
\*                  whose tuple conjunct pins n = DeepestKnownDepth(s, d.id).)
\*   prevtran     : the same-signer previous-message chain, transitively
\*                  closed: {x} together with the prevtran of the
\*                  deepestknown message for x's own signer, if there is
\*                  one (read off that entry's digest). By DeepestKnownPrev,
\*                  the chained message is a member of Prev(x).
\*   caught       : a subset of Acceptors, proven (CaughtRec) equal to
\*                  Caught(x): the union of the refs' caughts, plus the
\*                  signer of any candidate message (a ref, or a deepest-
\*                  known message of a ref) that is NOT on the prevtran
\*                  chain of the assembled deepestknown message for its own
\*                  signer -- such a message witnesses a same-signer fork.
\*   bal          : a Ballot, proven (BalRec) equal to B(x): the max of the
\*                  refs' bal values together with x's own proposal ballot
\*                  when x is a proposal ("1a"). (Under AlwaysAProposal the
\*                  candidate set is never empty: a refless message is a
\*                  proposal.)
\*   lrns         : the set of learners alpha with HasDepth(alpha, x, 1),
\*                  proven (LrnsRec) equal to Lrns(x), computed from the
\*                  refs' accumulators: frontier >= 1 needs only acceptor-
\*                  signedness (inherited quorum), frontier 0 needs the
\*                  pending level-0 attesters to form a quorum. IsTwoA is
\*                  then ~IsProposal /\ lrns # {} (IsTwoADigest).
\*   highesttwoas : a function mapping each learner l with an l-attesting
\*                  message in TranExclusive(x) (l \in Lrns of it -- usually
\*                  a 2a; the definition deliberately does not exclude
\*                  proposals, which Fresh must also see) to the DIGEST of
\*                  a maximal-ballot such message (CHOOSE among equal-ballot
\*                  ties; V is ballot-determined, so any tie works for
\*                  Fresh). Characterized by HighestTwoAsRec.
\*   fresh        : a function [Learners -> BOOLEAN], proven (FreshRec)
\*                  equal to Fresh(alpha, x): decided from highesttwoas,
\*                  caught (via ConFromCaught) and bal alone -- for each
\*                  connected learner's top attester, either it carries x's
\*                  value or some connected learner's top attester has a
\*                  strictly higher ballot.
\*   newbal       : boolean, proven (NewBalRec) equivalent to "every ref
\*                  has a strictly lower ballot than x". Descendants use it
\*                  to check IsOneB-ness of x without seeing x's refs.
\*   isoneb       : boolean, proven (IsOneBDigest) equivalent to IsOneB(x),
\*                  via the refs-local characterization of IsOneBRec: a
\*                  same-ballot proposal ref with newbal, all other refs
\*                  strictly lower.
\*   maxqdepth    : the same-ballot HISTORY ACCUMULATOR frontier: a map
\*                  from each learner alpha with an attester in Tran(x)
\*                  (some y with B(y) = B(x) and HasDepth(alpha, y, d)) to
\*                  the highest such d. Proven by MaxQDepthInv; the
\*                  own-HasDepth reading for acceptor-signed x is
\*                  MaxQDepthRec (via HasDepthDownward / AttesterInherit).
\*   pendingqd    : same domain; alpha |-> ALL frontier attesters
\*                  {y \in Tran(x) : B(y) = B(x) /\ HasDepth(alpha, y,
\*                  maxqdepth[alpha])} (inclusive of x). QdRec:
\*                  Qd(alpha, x, maxqdepth[alpha]+1) = pendingqd[alpha]\{x}.
EXTENDS MessageInterface

\* The candidate a ref's digest rc contributes for its own signer s: rc
\* itself (the whole digest), one level deeper than rc's own deepest entry
\* for s (depth 0 when s signs nothing in rc.id's exclusive history). Named
\* (rather than inlined in DeepestKnownCandidates) so FS_Image and friends
\* can match it by name.
DeepestKnownSignerCand(s, rc) ==
  <<(IF s \in DOMAIN rc.deepestknown
       THEN rc.deepestknown[s][1] + 1
       ELSE 0),
    rc>>

\* The candidate a ref's digest rc NOT signed by s passes through: its own
\* entry for s, unchanged.
DeepestKnownCarrierCand(s, rc) == rc.deepestknown[s]

\* All candidate <<depth, digest>> pairs for signer s, assembled from the
\* set r of refs' digests: each ref signed by s REPLACES its own deepest
\* entry with its whole digest (one deeper); each other ref passes its
\* entry for s through, when it has one.
DeepestKnownCandidates(s, r) ==
  {DeepestKnownSignerCand(s, rc) : rc \in {y \in r : Sig(y.id) = s}}
  \cup
  {DeepestKnownCarrierCand(s, rc) :
     rc \in {y \in r : Sig(y.id) # s /\ s \in DOMAIN y.deepestknown}}

\* The signers that get an entry: every ref's own signer, plus every signer
\* some ref already has an entry for. (Proven, for the refs' digests r,
\* equal to SigS(TranExclusive(x)).) Every member has at least one
\* candidate, by construction.
DeepestKnownSigners(r) ==
  {Sig(rc.id) : rc \in r} \cup UNION {DOMAIN rc.deepestknown : rc \in r}

\* For each signer, pick a candidate of maximal depth ("deepest").
DeepestKnownAssemble(r) ==
  [s \in DeepestKnownSigners(r) |->
     CHOOSE c \in DeepestKnownCandidates(s, r) :
       \A c2 \in DeepestKnownCandidates(s, r) : c[1] >= c2[1]]

\* x's same-signer chain: x itself, plus the prevtran carried by the
\* assembled entry for x's own signer, when there is one.
PrevTranAssemble(x, r) ==
  {x} \cup (IF Sig(x) \in DOMAIN DeepestKnownAssemble(r)
              THEN DeepestKnownAssemble(r)[Sig(x)][2].prevtran
              ELSE {})

\* The deepestknown messages a digest knows about: the message of each of
\* its entries.
DigestDKMessages(rc) ==
  {rc.deepestknown[s][2].id : s \in DOMAIN rc.deepestknown}

\* The messages whose chain membership the caught-assembly tests: every ref
\* itself, plus every deepestknown message of every ref.
CaughtCandidates(r) ==
  {rc.id : rc \in r} \cup UNION {DigestDKMessages(rc) : rc \in r}

\* The recursively-assembled caught set: everything the refs had already
\* caught, plus the signer of every candidate that has fallen off the
\* prevtran chain of the assembled deepestknown message for its signer
\* (evidence of a same-signer fork).
CaughtAssemble(r) ==
  (UNION {rc.caught : rc \in r})
  \cup SigS({y \in CaughtCandidates(r) :
               /\ Sig(y) \in Acceptors
               /\ y \notin DeepestKnownAssemble(r)[Sig(y)][2].prevtran})

\* The recursively-assembled ballot: the maximum of the refs' bal values,
\* plus x's own proposal ballot when x is a proposal.
BalAssemble(x, r) ==
  Max({rc.bal : rc \in r}
      \cup (IF IsProposal(x) THEN {ProposalBal(x)} ELSE {}))

\* The candidate an l-attesting entry of a ref's digest passes through
\* unchanged. Named so FS_Image can match it by name.
HTCarrierCand(l, rc) == rc.highesttwoas[l]

\* All candidate digests for learner l, from the set r of refs' digests:
\* each ref that itself attests for l (per its lrns field), plus each ref's
\* own entry for l, when it has one.
HTCandidates(l, r) ==
  {y \in r : l \in y.lrns}
  \cup {HTCarrierCand(l, rc) : rc \in {y \in r : l \in DOMAIN y.highesttwoas}}

\* The learners that get an entry: every learner some ref attests for,
\* plus every learner some ref already has an entry for.
HTLearners(r) ==
  (UNION {rc.lrns : rc \in r})
  \cup UNION {DOMAIN rc.highesttwoas : rc \in r}

\* For each learner, pick a candidate of maximal ballot ("highest").
HighestTwoAsAssemble(r) ==
  [l \in HTLearners(r) |->
     CHOOSE c \in HTCandidates(l, r) :
       \A c2 \in HTCandidates(l, r) : c.bal >= c2.bal]

\* The freshness decision for learner alpha, from the assembled fields
\* alone: for each connected learner's top attester, either it carries x's
\* value, or some connected learner's top attester strictly supersedes it.
\* Proven (FreshRec) equivalent to Fresh(alpha, x).
FreshAssemble(alpha, x, r) ==
  \A l \in ConFromCaught(alpha, CaughtAssemble(r))
             \cap DOMAIN HighestTwoAsAssemble(r) :
    \/ BalToVal(HighestTwoAsAssemble(r)[l].bal) = BalToVal(BalAssemble(x, r))
    \/ \E l2 \in ConFromCaught(alpha, CaughtAssemble(r))
                   \cap DOMAIN HighestTwoAsAssemble(r) :
         HighestTwoAsAssemble(r)[l2].bal > HighestTwoAsAssemble(r)[l].bal

\* x's ballot strictly exceeds all its refs' ballots.
NewBalAssemble(x, r) == \A rc \in r : rc.bal < BalAssemble(x, r)

\* IsOneB via the refs-local characterization (IsOneBRec): a same-ballot
\* proposal ref whose own refs are all strictly lower (its newbal), with
\* every other ref of x strictly lower too.
IsOneBAssemble(x, r) ==
  /\ ~IsProposal(x)
  /\ \E rc \in r :
       /\ IsProposal(rc.id)
       /\ rc.bal = BalAssemble(x, r)
       /\ rc.newbal
       /\ \A rc2 \in r : rc2 = rc \/ rc2.bal < BalAssemble(x, r)

\* The same-ballot refs: only their histories can hold same-ballot
\* attesters (B is monotone along Tran).
SBRefs(x, r) == {rc \in r : rc.bal = BalAssemble(x, r)}

\* Named projection so FS_Image can match by name.
QDepthCand(alpha, rc) == rc.maxqdepth[alpha]

QDepthCands(alpha, x, r) ==
  {QDepthCand(alpha, rc) :
     rc \in {y \in SBRefs(x, r) : alpha \in DOMAIN y.maxqdepth}}

\* The learners some same-ballot ref carries a frontier for.
QDom(x, r) == {alpha \in Learners :
                 \E rc \in SBRefs(x, r) : alpha \in DOMAIN rc.maxqdepth}

\* The highest frontier any same-ballot ref reports for alpha.
RefFrontier(alpha, x, r) == Max(QDepthCands(alpha, x, r))

\* Named projection so FS_Image can match by name.
RefPendingPart(alpha, rc) == rc.pendingqd[alpha]

\* The union of the frontier attester sets of the refs at the top frontier.
RefPending(alpha, x, r) ==
  UNION {RefPendingPart(alpha, rc) :
           rc \in {y \in SBRefs(x, r) :
                     /\ alpha \in DOMAIN y.maxqdepth
                     /\ y.maxqdepth[alpha] = RefFrontier(alpha, x, r)}}

\* x itself attests one level above the refs' frontier: it is acceptor-
\* signed and the pending attesters' signers form an alpha-quorum.
Bump(alpha, x, r) ==
  /\ Sig(x) \in Acceptors
  /\ SigS(RefPending(alpha, x, r)) \in Quorums(alpha)

\* x attests at level 0: an acceptor-signed fresh OneB.
SelfL0(alpha, x, r) ==
  /\ Sig(x) \in Acceptors
  /\ IsOneBAssemble(x, r)
  /\ FreshAssemble(alpha, x, r)

\* x attests at the refs' frontier level itself: for a frontier >= 1 any
\* acceptor-signed x inherits the level's quorum (AttesterInherit); at
\* frontier 0 it must be a fresh OneB.
SelfAtFrontier(alpha, x, r) ==
  IF RefFrontier(alpha, x, r) >= 1
    THEN Sig(x) \in Acceptors
    ELSE SelfL0(alpha, x, r)

\* The assembled domain: learners the refs carry, plus learners x newly
\* attests level 0 for.
MQDomain(x, r) ==
  QDom(x, r) \cup {alpha \in Learners : SelfL0(alpha, x, r)}

MaxQDepthAssemble(x, r) ==
  [alpha \in MQDomain(x, r) |->
     IF alpha \in QDom(x, r)
       THEN IF Bump(alpha, x, r)
              THEN RefFrontier(alpha, x, r) + 1
              ELSE RefFrontier(alpha, x, r)
       ELSE 0]

PendingQdAssemble(x, r) ==
  [alpha \in MQDomain(x, r) |->
     IF alpha \in QDom(x, r)
       THEN IF Bump(alpha, x, r)
              THEN {x}
              ELSE RefPending(alpha, x, r)
                     \cup (IF SelfAtFrontier(alpha, x, r) THEN {x} ELSE {})
       ELSE {x}]

\* The learners x itself attests depth 1 for, decidable from the refs'
\* accumulators: with a frontier >= 1 any acceptor-signed x inherits a
\* level-1 quorum (AttesterInherit + HasDepthDownward); at frontier 0 the
\* pending level-0 attesters must form a quorum (Bump); with no frontier
\* there are no level-0 attesters at all, and quorums are never empty.
LrnsAssemble(x, r) ==
  {alpha \in QDom(x, r) :
     IF RefFrontier(alpha, x, r) >= 1
       THEN Sig(x) \in Acceptors
       ELSE Bump(alpha, x, r)}

\* The assembly step handed to RecursiveMessageRefsFunc. r is the set of
\* refs' digests; when Refs(x) = {} (equivalently TranExclusive(x) = {}),
\* deepestknown is the empty function, prevtran is {x}, caught is {}, bal
\* is x's own proposal ballot (a refless message is a proposal, under
\* AlwaysAProposal), highesttwoas is the empty function, fresh is
\* everywhere TRUE, newbal is TRUE, isoneb is FALSE, and maxqdepth /
\* pendingqd have an entry (0 / {x}) exactly for the learners x attests
\* level 0 for.
DigestR(x, r) ==
  [ id           |-> x,
    deepestknown |-> DeepestKnownAssemble(r),
    prevtran     |-> PrevTranAssemble(x, r),
    caught       |-> CaughtAssemble(r),
    bal          |-> BalAssemble(x, r),
    lrns         |-> LrnsAssemble(x, r),
    highesttwoas |-> HighestTwoAsAssemble(r),
    fresh        |-> [alpha \in Learners |-> FreshAssemble(alpha, x, r)],
    newbal       |-> NewBalAssemble(x, r),
    isoneb       |-> IsOneBAssemble(x, r),
    maxqdepth    |-> MaxQDepthAssemble(x, r),
    pendingqd    |-> PendingQdAssemble(x, r) ]

Digest(x) == RecursiveMessageRefsFunc(DigestR, x)

DeepestKnown(x) == Digest(x).deepestknown

PrevTran(x) == Digest(x).prevtran

DigestCaught(x) == Digest(x).caught

DigestBal(x) == Digest(x).bal

DigestLrns(x) == Digest(x).lrns

DigestHighestTwoAs(x) == Digest(x).highesttwoas

DigestFresh(x) == Digest(x).fresh

DigestNewBal(x) == Digest(x).newbal

DigestIsOneB(x) == Digest(x).isoneb

DigestMaxQDepth(x) == Digest(x).maxqdepth

DigestPendingQd(x) == Digest(x).pendingqd

\* The chain depth message w would have as a candidate for signer s: one
\* more than w's own deepest entry for s, or 0 if it has none.
DeepestKnownDepth(s, w) ==
  IF s \in DOMAIN DeepestKnown(w) THEN DeepestKnown(w)[s][1] + 1 ELSE 0

\* The structural invariant of deepestknown, proven for every message by
\* DeepestKnownInv (via DeepestKnownStep + RefsInduction): the domain is
\* exactly the signers of the exclusive transitive history, and each entry
\* is a <<depth, digest>> pair -- the digest is the CANONICAL digest of its
\* own message (first conjunct below), which realizes the maximal chain
\* depth for its signer.
DeepestKnownInvariant(m) ==
  /\ DOMAIN DeepestKnown(m) = SigS(TranExclusive(m))
  /\ \A s \in DOMAIN DeepestKnown(m) :
       /\ DeepestKnown(m)[s][2] = Digest(DeepestKnown(m)[s][2].id)
       /\ DeepestKnown(m)[s][2].id \in TranExclusive(m)
       /\ Sig(DeepestKnown(m)[s][2].id) = s
       /\ DeepestKnown(m)[s][1] \in Nat
       /\ DeepestKnown(m)[s]
            = <<DeepestKnownDepth(s, DeepestKnown(m)[s][2].id),
                DeepestKnown(m)[s][2]>>
       /\ \A w \in TranExclusive(m) : Sig(w) = s =>
            /\ DeepestKnownDepth(s, w) \in Nat
            /\ DeepestKnownDepth(s, w) <= DeepestKnown(m)[s][1]

\* The structural invariant of highesttwoas, proven for every message by
\* HighestTwoAsRec: the domain is exactly the learners attested for
\* somewhere in the exclusive history, and each entry is the canonical
\* digest of an l-attesting message of maximal ballot.
HighestTwoAsInvariant(m) ==
  /\ DOMAIN DigestHighestTwoAs(m)
       = {l \in Learners : \E y \in TranExclusive(m) : l \in Lrns(y)}
  /\ \A l \in DOMAIN DigestHighestTwoAs(m) :
       /\ DigestHighestTwoAs(m)[l] = Digest(DigestHighestTwoAs(m)[l].id)
       /\ DigestHighestTwoAs(m)[l].id \in TranExclusive(m)
       /\ l \in Lrns(DigestHighestTwoAs(m)[l].id)
       /\ \A y \in TranExclusive(m) :
            l \in Lrns(y) => B(y) <= B(DigestHighestTwoAs(m)[l].id)

\* The structural invariant of maxqdepth/pendingqd, proven for every
\* message by MaxQDepthInv: the domain is exactly the learners with a
\* same-ballot attester in the INCLUSIVE history, the frontier value is
\* attained and maximal, and pendingqd collects exactly the frontier
\* attesters.
MaxQDepthInvariant(m) ==
  /\ DOMAIN DigestMaxQDepth(m)
       = {alpha \in Learners :
            \E y \in Tran(m) : /\ B(y) = B(m)
                               /\ \E d \in Nat : HasDepth(alpha, y, d)}
  /\ DOMAIN DigestPendingQd(m) = DOMAIN DigestMaxQDepth(m)
  /\ \A alpha \in DOMAIN DigestMaxQDepth(m) :
       /\ DigestMaxQDepth(m)[alpha] \in Nat
       /\ \E y \in Tran(m) :
            /\ B(y) = B(m)
            /\ HasDepth(alpha, y, DigestMaxQDepth(m)[alpha])
       /\ \A y \in Tran(m) : \A d \in Nat :
            (B(y) = B(m) /\ HasDepth(alpha, y, d))
              => d <= DigestMaxQDepth(m)[alpha]
       /\ DigestPendingQd(m)[alpha]
            = {y \in Tran(m) :
                 /\ B(y) = B(m)
                 /\ HasDepth(alpha, y, DigestMaxQDepth(m)[alpha])}

\* The combined per-message invariant proven by the single mutual
\* induction DigestInv: the highesttwoas and maxqdepth/pendingqd
\* invariants together with the correctness of the recursive lrns field.
\* (They are mutually dependent across a message and its refs: highesttwoas
\* reads refs' lrns; fresh reads highesttwoas; the frontier's level-0 base
\* reads fresh; lrns reads the frontier.)
DigestInvariant(m) ==
  /\ HighestTwoAsInvariant(m)
  /\ MaxQDepthInvariant(m)
  /\ DigestLrns(m) = Lrns(m)

\* ------------------------------------------------------------------------
\* Parameterized correctness predicates: the invariant bodies with the
\* stored field replaced by an arbitrary value. XxxInvariant(m) is
\* definitionally XxxCorrect(m, <the field>); the generalized step lemmas
\* prove XxxCorrect for assemblies over ANY digest set {Digest(p) : p \in S}
\* with Refs(m) \subseteq S \subseteq TranExclusive(m) -- the shape a
\* candidate's priors take in the concrete world.
\* ------------------------------------------------------------------------

DeepestKnownCorrect(m, dk) ==
  /\ DOMAIN dk = SigS(TranExclusive(m))
  /\ \A s \in DOMAIN dk :
       /\ dk[s][2] = Digest(dk[s][2].id)
       /\ dk[s][2].id \in TranExclusive(m)
       /\ Sig(dk[s][2].id) = s
       /\ dk[s][1] \in Nat
       /\ dk[s] = <<DeepestKnownDepth(s, dk[s][2].id), dk[s][2]>>
       /\ \A w \in TranExclusive(m) : Sig(w) = s =>
            /\ DeepestKnownDepth(s, w) \in Nat
            /\ DeepestKnownDepth(s, w) <= dk[s][1]

HighestTwoAsCorrect(m, ht) ==
  /\ DOMAIN ht = {l \in Learners : \E y \in TranExclusive(m) : l \in Lrns(y)}
  /\ \A l \in DOMAIN ht :
       /\ ht[l] = Digest(ht[l].id)
       /\ ht[l].id \in TranExclusive(m)
       /\ l \in Lrns(ht[l].id)
       /\ \A y \in TranExclusive(m) :
            l \in Lrns(y) => B(y) <= B(ht[l].id)

MaxQDepthCorrect(m, mq, pq) ==
  /\ DOMAIN mq
       = {alpha \in Learners :
            \E y \in Tran(m) : /\ B(y) = B(m)
                               /\ \E d \in Nat : HasDepth(alpha, y, d)}
  /\ DOMAIN pq = DOMAIN mq
  /\ \A alpha \in DOMAIN mq :
       /\ mq[alpha] \in Nat
       /\ \E y \in Tran(m) :
            /\ B(y) = B(m)
            /\ HasDepth(alpha, y, mq[alpha])
       /\ \A y \in Tran(m) : \A d \in Nat :
            (B(y) = B(m) /\ HasDepth(alpha, y, d))
              => d <= mq[alpha]
       /\ pq[alpha]
            = {y \in Tran(m) :
                 /\ B(y) = B(m)
                 /\ HasDepth(alpha, y, mq[alpha])}
====================================================================
