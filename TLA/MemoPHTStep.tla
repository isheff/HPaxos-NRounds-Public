------------------------------ MODULE MemoPHTStep ------------------------------
\* MemoP tower, leg S2: the highesttwoas assembly over the priors' MemoP
\* records has the right domain, and each entry's BALLOT is attained by, and
\* bounds, every l-attesting message of x's exclusive history.
\*
\* Unlike the value-determined legs, this one does NOT transport the result
\* from the canonical assembly over {Memo(q) : q \in priors}: the assembled
\* entry is a CHOOSE among tied maximal-ballot candidates, and the P-side
\* candidate set contains extra (prior-but-not-ref) records, so the two
\* assemblies may legitimately pick different entry RECORDS.  Only the
\* ballot is value-determined, so this leg re-runs HighestTwoAsStep's
\* maximum argument over the MemoP records, reading the members' ballots,
\* attestations and entry-ballots off the induction hypothesis.
EXTENDS MemoPDefs, CRefsSubPriors, TranExclusiveCover, TranSubMessages,
        BBallot, BalFldMaxExists, FiniteSetTheorems,
        CFields, CMessageTranClosed, CTranResolve
LOCAL INSTANCE TLAPS

LEMMA MemoPHTStep ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         AlwaysAProposal, MessageInterface = CMI,
         NEW x \in CMessages,
         \A y \in CTranExcl(x) : MemoPGood(y)
  PROVE /\ DOMAIN HighestTwoAsAssemble({MemoP(q) : q \in x.priors})
             = {l \in Learners : \E y \in TranExclusive(x) : l \in Lrns(y)}
        /\ \A l \in DOMAIN HighestTwoAsAssemble({MemoP(q) : q \in x.priors}) :
             /\ \E y \in TranExclusive(x) :
                  /\ l \in Lrns(y)
                  /\ B(y)
                       = HighestTwoAsAssemble({MemoP(q) : q \in x.priors})[l].bal
             /\ \A y \in TranExclusive(x) :
                  l \in Lrns(y) =>
                    B(y)
                      <= HighestTwoAsAssemble({MemoP(q) : q \in x.priors})[l].bal
<1> DEFINE pr == x.priors
<1> DEFINE rP == {MemoP(q) : q \in pr}
<1> DEFINE hta == HighestTwoAsAssemble(rP)
<1> DEFINE HP(q) == MemoP(q).highesttwoas
\* ------------------------------------------------------------------ prelude
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
<1>prMsg. pr \subseteq Messages  BY <1>prM, CFields
<1>tex. TranExclusive(x) = UNION {Tran(p) : p \in pr}
  BY <1>xm, <1>sand, TranExclusiveCover
<1>texPP. \A q \in pr : TranExclusive(q) \subseteq TranExclusive(x)
  BY <1>tex DEF TranExclusive
<1>pTE. \A q \in pr : q \in TranExclusive(x)  BY <1>sand
<1>teM. TranExclusive(x) \subseteq Messages
  BY <1>xm, TranSubMessages DEF TranExclusive
\* ------------------------------------------------- member projections (IH)
<1>lrnsp. \A q \in pr : MemoP(q).lrns = Lrns(q)
  BY <1>ihq DEF MemoPGood
<1>balp. \A q \in pr : MemoP(q).bal = B(q)
  BY <1>ihq DEF MemoPGood
<1>htdomp. \A q \in pr :
             DOMAIN HP(q)
               = {l \in Learners : \E y \in TranExclusive(q) : l \in Lrns(y)}
  BY <1>ihq DEF MemoPGood
<1>htentp. \A q \in pr : \A l \in DOMAIN HP(q) :
             /\ \E y \in TranExclusive(q) :
                  l \in Lrns(y) /\ B(y) = HP(q)[l].bal
             /\ \A y \in TranExclusive(q) :
                  l \in Lrns(y) => B(y) <= HP(q)[l].bal
  BY <1>ihq DEF MemoPGood
\* ------------------------------------------------------------------- domain
<1>dom0. DOMAIN hta = HTLearners(rP)
  BY DEF HighestTwoAsAssemble
<1>lrnseq. UNION {rc.lrns : rc \in rP} = UNION {Lrns(q) : q \in pr}
  <2>sub. UNION {rc.lrns : rc \in rP} \subseteq UNION {Lrns(q) : q \in pr}
    <3> SUFFICES ASSUME NEW l \in UNION {rc.lrns : rc \in rP}
        PROVE l \in UNION {Lrns(q) : q \in pr}  OBVIOUS
    <3>1. PICK rc \in rP : l \in rc.lrns  OBVIOUS
    <3>2. PICK q \in pr : rc = MemoP(q)  BY <3>1
    <3> QED BY <3>1, <3>2, <1>lrnsp
  <2>sup. UNION {Lrns(q) : q \in pr} \subseteq UNION {rc.lrns : rc \in rP}
    <3> SUFFICES ASSUME NEW q \in pr, NEW l \in Lrns(q)
        PROVE l \in UNION {rc.lrns : rc \in rP}  OBVIOUS
    <3>1. MemoP(q) \in rP  OBVIOUS
    <3> QED BY <3>1, <1>lrnsp
  <2> QED BY <2>sub, <2>sup
<1>htdomeq. UNION {DOMAIN rc.highesttwoas : rc \in rP}
              = UNION {DOMAIN HP(q) : q \in pr}
  <2>sub. UNION {DOMAIN rc.highesttwoas : rc \in rP}
            \subseteq UNION {DOMAIN HP(q) : q \in pr}
    <3> SUFFICES ASSUME NEW l \in UNION {DOMAIN rc.highesttwoas : rc \in rP}
        PROVE l \in UNION {DOMAIN HP(q) : q \in pr}  OBVIOUS
    <3>1. PICK rc \in rP : l \in DOMAIN rc.highesttwoas  OBVIOUS
    <3>2. PICK q \in pr : rc = MemoP(q)  BY <3>1
    <3> QED BY <3>1, <3>2
  <2>sup. UNION {DOMAIN HP(q) : q \in pr}
            \subseteq UNION {DOMAIN rc.highesttwoas : rc \in rP}
    <3> SUFFICES ASSUME NEW q \in pr, NEW l \in DOMAIN HP(q)
        PROVE l \in UNION {DOMAIN rc.highesttwoas : rc \in rP}  OBVIOUS
    <3>1. MemoP(q) \in rP  OBVIOUS
    <3> QED BY <3>1
  <2> QED BY <2>sub, <2>sup
<1>domchar. (UNION {Lrns(q) : q \in pr}) \cup UNION {DOMAIN HP(q) : q \in pr}
              = {l \in Learners : \E y \in TranExclusive(x) : l \in Lrns(y)}
  <2>sub. (UNION {Lrns(q) : q \in pr}) \cup UNION {DOMAIN HP(q) : q \in pr}
            \subseteq {l \in Learners :
                         \E y \in TranExclusive(x) : l \in Lrns(y)}
    <3>1. \A q \in pr : Lrns(q) \subseteq
            {l \in Learners : \E y \in TranExclusive(x) : l \in Lrns(y)}
      <4> SUFFICES ASSUME NEW q \in pr, NEW l \in Lrns(q)
          PROVE l \in {ll \in Learners :
                         \E y \in TranExclusive(x) : ll \in Lrns(y)}
        OBVIOUS
      <4>1. l \in Learners  BY DEF Lrns
      <4> QED BY <4>1, <1>pTE
    <3>2. \A q \in pr : DOMAIN HP(q) \subseteq
            {l \in Learners : \E y \in TranExclusive(x) : l \in Lrns(y)}
      <4> SUFFICES ASSUME NEW q \in pr, NEW l \in DOMAIN HP(q)
          PROVE l \in {ll \in Learners :
                         \E y \in TranExclusive(x) : ll \in Lrns(y)}
        OBVIOUS
      <4>1. l \in Learners /\ \E y \in TranExclusive(q) : l \in Lrns(y)
        BY <1>htdomp
      <4> QED BY <4>1, <1>texPP
    <3> QED BY <3>1, <3>2
  <2>sup. {l \in Learners : \E y \in TranExclusive(x) : l \in Lrns(y)}
            \subseteq (UNION {Lrns(q) : q \in pr})
                        \cup UNION {DOMAIN HP(q) : q \in pr}
    <3> SUFFICES ASSUME NEW l \in Learners,
                        NEW y \in TranExclusive(x), l \in Lrns(y)
        PROVE l \in (UNION {Lrns(q) : q \in pr})
                      \cup UNION {DOMAIN HP(q) : q \in pr}
      OBVIOUS
    <3>p. PICK q \in pr : y \in Tran(q)  BY <1>tex
    <3>a. CASE y = q
      <4> QED BY <3>a, <3>p
    <3>b. CASE y # q
      <4>1. y \in TranExclusive(q)  BY <3>p, <3>b DEF TranExclusive
      <4>2. l \in DOMAIN HP(q)  BY <4>1, <1>htdomp
      <4> QED BY <3>p, <4>2
    <3> QED BY <3>a, <3>b
  <2> QED BY <2>sub, <2>sup
<1>dom. DOMAIN hta
          = {l \in Learners : \E y \in TranExclusive(x) : l \in Lrns(y)}
  BY <1>dom0, <1>lrnseq, <1>htdomeq, <1>domchar DEF HTLearners
\* -------------------------------------------------------------------- per-l
<1>main. \A l \in DOMAIN hta :
       /\ \E y \in TranExclusive(x) : l \in Lrns(y) /\ B(y) = hta[l].bal
       /\ \A y \in TranExclusive(x) : l \in Lrns(y) => B(y) <= hta[l].bal
  <2> SUFFICES ASSUME NEW l \in DOMAIN hta
      PROVE /\ \E y \in TranExclusive(x) : l \in Lrns(y) /\ B(y) = hta[l].bal
            /\ \A y \in TranExclusive(x) : l \in Lrns(y) => B(y) <= hta[l].bal
    OBVIOUS
  <2> DEFINE C == HTCandidates(l, rP)
  <2>lL. l \in Learners  BY <1>dom
  <2>sD. l \in HTLearners(rP)  BY <1>dom0
  <2>ent. hta[l]
            = CHOOSE c \in HTCandidates(l, rP) :
                \A c2 \in HTCandidates(l, rP) : c.bal >= c2.bal
    BY <2>sD DEF HighestTwoAsAssemble
  <2>candR. \A q \in pr : l \in Lrns(q) => MemoP(q) \in C
    <3> SUFFICES ASSUME NEW q \in pr, l \in Lrns(q)
        PROVE MemoP(q) \in C  OBVIOUS
    <3>1. MemoP(q) \in rP  OBVIOUS
    <3>2. l \in MemoP(q).lrns  BY <1>lrnsp
    <3>3. MemoP(q) \in {y \in rP : l \in y.lrns}  BY <3>1, <3>2
    <3> QED BY <3>3 DEF HTCandidates
  <2>candC. \A q \in pr : l \in DOMAIN HP(q) => HP(q)[l] \in C
    <3> SUFFICES ASSUME NEW q \in pr, l \in DOMAIN HP(q)
        PROVE HP(q)[l] \in C  OBVIOUS
    <3>1. MemoP(q) \in rP  OBVIOUS
    <3>2. MemoP(q) \in {y \in rP : l \in DOMAIN y.highesttwoas}
      BY <3>1
    <3>3. HTCarrierCand(l, MemoP(q)) = HP(q)[l]  BY DEF HTCarrierCand
    <3> QED BY <3>2, <3>3 DEF HTCandidates
  <2>sound. \A c \in C :
              \E y \in TranExclusive(x) : l \in Lrns(y) /\ B(y) = c.bal
    <3> SUFFICES ASSUME NEW c \in C
        PROVE \E y \in TranExclusive(x) : l \in Lrns(y) /\ B(y) = c.bal
      OBVIOUS
    <3>split. \/ c \in {y \in rP : l \in y.lrns}
              \/ c \in {HTCarrierCand(l, rc) :
                          rc \in {y \in rP : l \in DOMAIN y.highesttwoas}}
      BY DEF HTCandidates
    <3>a. CASE c \in {y \in rP : l \in y.lrns}
      <4>1. PICK q \in pr : c = MemoP(q)  BY <3>a
      <4>2. l \in MemoP(q).lrns  BY <3>a, <4>1
      <4>3. l \in Lrns(q)  BY <4>2, <1>lrnsp
      <4>4. c.bal = B(q)  BY <4>1, <1>balp
      <4> QED BY <4>3, <4>4, <1>pTE
    <3>b. CASE c \in {HTCarrierCand(l, rc) :
                        rc \in {y \in rP : l \in DOMAIN y.highesttwoas}}
      <4>rc. PICK rc \in {y \in rP : l \in DOMAIN y.highesttwoas} :
               c = HTCarrierCand(l, rc)
        BY <3>b
      <4>q. PICK q \in pr : rc = MemoP(q)  BY <4>rc
      <4>c2. c = HP(q)[l] /\ l \in DOMAIN HP(q)
        BY <4>rc, <4>q DEF HTCarrierCand
      <4>w. PICK y \in TranExclusive(q) :
              l \in Lrns(y) /\ B(y) = HP(q)[l].bal
        BY <4>q, <4>c2, <1>htentp
      <4> QED BY <4>c2, <4>w, <1>texPP
    <3> QED BY <3>split, <3>a, <3>b
  <2>balc. \A c \in C : c.bal \in Nat
    <3> SUFFICES ASSUME NEW c \in C PROVE c.bal \in Nat  OBVIOUS
    <3>1. PICK y \in TranExclusive(x) : l \in Lrns(y) /\ B(y) = c.bal
      BY <2>sound
    <3>2. y \in Messages  BY <3>1, <1>teM
    <3>3. B(y) \in Ballots  BY <3>2, BBallot
    <3> QED BY <3>1, <3>3 DEF Ballots
  <2>ne. C # {}
    <3>1. \/ l \in UNION {rc.lrns : rc \in rP}
          \/ l \in UNION {DOMAIN rc.highesttwoas : rc \in rP}
      BY <2>sD DEF HTLearners
    <3>a. CASE l \in UNION {rc.lrns : rc \in rP}
      <4>1. l \in UNION {Lrns(q) : q \in pr}  BY <3>a, <1>lrnseq
      <4>2. PICK q \in pr : l \in Lrns(q)  BY <4>1
      <4> QED BY <4>2, <2>candR
    <3>b. CASE l \in UNION {DOMAIN rc.highesttwoas : rc \in rP}
      <4>1. l \in UNION {DOMAIN HP(q) : q \in pr}  BY <3>b, <1>htdomeq
      <4>2. PICK q \in pr : l \in DOMAIN HP(q)  BY <4>1
      <4> QED BY <4>2, <2>candC
    <3> QED BY <3>1, <3>a, <3>b
  <2>fin. IsFiniteSet(C)
    <3>ftx. IsFiniteSet(Tran(x))  BY <1>xm DEF TranFinite
    <3>fpr. IsFiniteSet(pr)
      <4>1. pr \subseteq Tran(x)  BY <1>sand DEF TranExclusive
      <4> QED BY <4>1, <3>ftx, FS_Subset
    <3>frP. IsFiniteSet(rP)  BY <3>fpr, FS_Image
    <3>f1. IsFiniteSet({y \in rP : l \in y.lrns})  BY <3>frP, FS_Subset
    <3>f2. IsFiniteSet({y \in rP : l \in DOMAIN y.highesttwoas})
      BY <3>frP, FS_Subset
    <3>fC. IsFiniteSet({HTCarrierCand(l, rc) :
                          rc \in {y \in rP : l \in DOMAIN y.highesttwoas}})
      BY <3>f2, FS_Image
    <3> QED BY <3>f1, <3>fC, FS_Union DEF HTCandidates
  <2>maxE. \E c \in C : \A c2 \in C : c.bal >= c2.bal
    BY <2>fin, <2>ne, <2>balc, BalFldMaxExists
  <2>win. /\ hta[l] \in C
          /\ \A c2 \in C : hta[l].bal >= c2.bal
    BY <2>ent, <2>maxE
  <2>wnat. hta[l].bal \in Nat  BY <2>win, <2>balc
  <2>attain. \E y \in TranExclusive(x) :
               l \in Lrns(y) /\ B(y) = hta[l].bal
    BY <2>win, <2>sound
  <2>hi. \A y \in TranExclusive(x) : l \in Lrns(y) => B(y) <= hta[l].bal
    <3> SUFFICES ASSUME NEW y \in TranExclusive(x), l \in Lrns(y)
        PROVE B(y) <= hta[l].bal
      OBVIOUS
    <3>p. PICK q \in pr : y \in Tran(q)  BY <1>tex
    <3>ynat. B(y) \in Nat
      <4>1. y \in Messages  BY <1>teM
      <4>2. B(y) \in Ballots  BY <4>1, BBallot
      <4> QED BY <4>2 DEF Ballots
    <3>a. CASE y = q
      <4>c. MemoP(q) \in C  BY <3>a, <2>candR
      <4>cb. MemoP(q).bal = B(q)  BY <1>balp
      <4>le. hta[l].bal >= MemoP(q).bal  BY <4>c, <2>win
      <4>nat. MemoP(q).bal \in Nat  BY <4>c, <2>balc
      <4> QED BY <3>a, <4>cb, <4>le, <4>nat, <2>wnat, <3>ynat, SMT
    <3>b. CASE y # q
      <4>yTE. y \in TranExclusive(q)  BY <3>p, <3>b DEF TranExclusive
      <4>ldom. l \in DOMAIN HP(q)  BY <2>lL, <4>yTE, <1>htdomp
      <4>c. HP(q)[l] \in C  BY <4>ldom, <2>candC
      <4>bound. B(y) <= HP(q)[l].bal
        BY <4>ldom, <4>yTE, <1>htentp
      <4>nat. HP(q)[l].bal \in Nat  BY <4>c, <2>balc
      <4>le. hta[l].bal >= HP(q)[l].bal  BY <4>c, <2>win
      <4> QED BY <4>bound, <4>le, <4>nat, <2>wnat, <3>ynat, SMT
    <3> QED BY <3>a, <3>b
  <2> QED BY <2>attain, <2>hi
<1> QED BY <1>dom, <1>main
=============================================================================
