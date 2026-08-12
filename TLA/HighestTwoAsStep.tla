------------------------- MODULE HighestTwoAsStep -------------------------
\*   DigestRec, TranExclusiveRefs, TranSubMessages, BalRec, BBallot,
\*   BalFldMaxExists -> cited lemmas
\*   FiniteSetTheorems -> FS_Subset, FS_Image, FS_Union
\*   TLAPS -> SMT; proof-only
EXTENDS RecursiveWellFormed, DigestRec, TranExclusiveCover, TranSubMessages,
        BalRec, BBallot, BalFldMaxExists, FiniteSetTheorems
LOCAL INSTANCE TLAPS

\* The generalized step for the highesttwoas part of DigestInv: given
\* correct digests for ANY set S between Refs(x) and TranExclusive(x), the
\* assembly over S's digests is a correct highesttwoas map for x. Lrns
\* stays opaque throughout: members report their own attestations via the
\* lrns field, entries pass through carriers, and ballots compare via the
\* digests' bal fields (= B, by BalRec).
LEMMA HighestTwoAsStep ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         AlwaysAProposal,
         NEW x \in Messages,
         NEW S, Refs(x) \subseteq S, S \subseteq TranExclusive(x),
         \A p \in S : DigestLrns(p) = Lrns(p),
         \A p \in S : HighestTwoAsInvariant(p)
  PROVE HighestTwoAsCorrect(x, HighestTwoAsAssemble({Digest(p) : p \in S}))
<1> DEFINE R == S
<1> DEFINE recs == {Digest(p) : p \in R}
<1> DEFINE hta == HighestTwoAsAssemble(recs)
<1>ih. \A p \in R : HighestTwoAsInvariant(p)  OBVIOUS
<1>rsub. R \subseteq TranExclusive(x)  OBVIOUS
<1>rM. R \subseteq Messages  BY <1>rsub, TranSubMessages DEF TranExclusive
<1>tex. TranExclusive(x) = UNION {Tran(p) : p \in R}  BY TranExclusiveCover
<1>texPP. \A p \in R : TranExclusive(p) \subseteq TranExclusive(x)
  BY <1>tex DEF TranExclusive
<1>pTE. \A p \in R : p \in TranExclusive(x)  BY <1>rsub
<1>teM. TranExclusive(x) \subseteq Messages
  BY TranSubMessages DEF TranExclusive
<1>idp. \A p \in R : /\ Digest(p).id = p
                     /\ Digest(p).lrns = Lrns(p)
                     /\ Digest(p).highesttwoas = DigestHighestTwoAs(p)
                     /\ Digest(p).bal = B(p)
  <2> SUFFICES ASSUME NEW p \in R
      PROVE /\ Digest(p).id = p
            /\ Digest(p).lrns = Lrns(p)
            /\ Digest(p).highesttwoas = DigestHighestTwoAs(p)
            /\ Digest(p).bal = B(p)
    OBVIOUS
  <2>1. p \in Messages  BY <1>rM
  <2>2. Digest(p) = DigestR(p, {Digest(q) : q \in Refs(p)})
    BY <2>1, DigestRec
  <2>3. DigestBal(p) = B(p)  BY <2>1, BalRec
  <2>4. DigestLrns(p) = Lrns(p)  OBVIOUS
  <2> QED BY <2>2, <2>3, <2>4
    DEF DigestR, DigestHighestTwoAs, DigestBal, DigestLrns
<1>dom0. DOMAIN hta = HTLearners(recs)
  BY DEF HighestTwoAsAssemble
<1>ihdom. \A p \in R : DOMAIN DigestHighestTwoAs(p)
            = {l \in Learners : \E y \in TranExclusive(p) : l \in Lrns(y)}
  BY <1>ih DEF HighestTwoAsInvariant
\* ------------------------------------------------------------------ domain
<1>lrnseq. UNION {rc.lrns : rc \in recs} = UNION {Lrns(p) : p \in R}
  <2>1. \A p \in R : Digest(p).lrns = Lrns(p)  BY <1>idp
  <2>sub. UNION {rc.lrns : rc \in recs} \subseteq UNION {Lrns(p) : p \in R}
    <3> SUFFICES ASSUME NEW l \in UNION {rc.lrns : rc \in recs}
        PROVE l \in UNION {Lrns(p) : p \in R}  OBVIOUS
    <3>1. PICK rc \in recs : l \in rc.lrns  OBVIOUS
    <3>2. PICK p \in R : rc = Digest(p)  OBVIOUS
    <3> QED BY <3>1, <3>2, <2>1
  <2>sup. UNION {Lrns(p) : p \in R} \subseteq UNION {rc.lrns : rc \in recs}
    <3> SUFFICES ASSUME NEW p \in R, NEW l \in Lrns(p)
        PROVE l \in UNION {rc.lrns : rc \in recs}  OBVIOUS
    <3>1. Digest(p) \in recs  OBVIOUS
    <3> QED BY <3>1, <2>1
  <2> QED BY <2>sub, <2>sup
<1>htdomeq. UNION {DOMAIN rc.highesttwoas : rc \in recs}
              = UNION {DOMAIN DigestHighestTwoAs(p) : p \in R}
  <2>1. \A p \in R : DOMAIN Digest(p).highesttwoas
                       = DOMAIN DigestHighestTwoAs(p)
    BY <1>idp
  <2>sub. UNION {DOMAIN rc.highesttwoas : rc \in recs}
            \subseteq UNION {DOMAIN DigestHighestTwoAs(p) : p \in R}
    <3> SUFFICES ASSUME NEW l \in UNION {DOMAIN rc.highesttwoas : rc \in recs}
        PROVE l \in UNION {DOMAIN DigestHighestTwoAs(p) : p \in R}  OBVIOUS
    <3>1. PICK rc \in recs : l \in DOMAIN rc.highesttwoas  OBVIOUS
    <3>2. PICK p \in R : rc = Digest(p)  OBVIOUS
    <3> QED BY <3>1, <3>2, <2>1
  <2>sup. UNION {DOMAIN DigestHighestTwoAs(p) : p \in R}
            \subseteq UNION {DOMAIN rc.highesttwoas : rc \in recs}
    <3> SUFFICES ASSUME NEW p \in R, NEW l \in DOMAIN DigestHighestTwoAs(p)
        PROVE l \in UNION {DOMAIN rc.highesttwoas : rc \in recs}  OBVIOUS
    <3>1. Digest(p) \in recs  OBVIOUS
    <3> QED BY <3>1, <2>1
  <2> QED BY <2>sub, <2>sup
<1>domchar. (UNION {Lrns(p) : p \in R})
              \cup UNION {DOMAIN DigestHighestTwoAs(p) : p \in R}
            = {l \in Learners : \E y \in TranExclusive(x) : l \in Lrns(y)}
  <2>sub. (UNION {Lrns(p) : p \in R})
              \cup UNION {DOMAIN DigestHighestTwoAs(p) : p \in R}
            \subseteq {l \in Learners : \E y \in TranExclusive(x) : l \in Lrns(y)}
    <3>1. \A p \in R : Lrns(p) \subseteq
            {l \in Learners : \E y \in TranExclusive(x) : l \in Lrns(y)}
      <4> SUFFICES ASSUME NEW p \in R, NEW l \in Lrns(p)
          PROVE l \in {ll \in Learners : \E y \in TranExclusive(x) : ll \in Lrns(y)}
        OBVIOUS
      <4>1. l \in Learners  BY DEF Lrns
      <4> QED BY <4>1, <1>pTE
    <3>2. \A p \in R : DOMAIN DigestHighestTwoAs(p) \subseteq
            {l \in Learners : \E y \in TranExclusive(x) : l \in Lrns(y)}
      <4> SUFFICES ASSUME NEW p \in R, NEW l \in DOMAIN DigestHighestTwoAs(p)
          PROVE l \in {ll \in Learners : \E y \in TranExclusive(x) : ll \in Lrns(y)}
        OBVIOUS
      <4>1. l \in Learners /\ \E y \in TranExclusive(p) : l \in Lrns(y)
        BY <1>ihdom
      <4> QED BY <4>1, <1>texPP
    <3> QED BY <3>1, <3>2
  <2>sup. {l \in Learners : \E y \in TranExclusive(x) : l \in Lrns(y)}
            \subseteq (UNION {Lrns(p) : p \in R})
                        \cup UNION {DOMAIN DigestHighestTwoAs(p) : p \in R}
    <3> SUFFICES ASSUME NEW l \in Learners,
                        NEW y \in TranExclusive(x), l \in Lrns(y)
        PROVE l \in (UNION {Lrns(p) : p \in R})
                      \cup UNION {DOMAIN DigestHighestTwoAs(p) : p \in R}
      OBVIOUS
    <3>p. PICK p \in R : y \in Tran(p)  BY <1>tex
    <3>a. CASE y = p
      <4> QED BY <3>a, <3>p
    <3>b. CASE y # p
      <4>1. y \in TranExclusive(p)  BY <3>p, <3>b DEF TranExclusive
      <4>2. l \in DOMAIN DigestHighestTwoAs(p)  BY <4>1, <1>ihdom
      <4> QED BY <3>p, <4>2
    <3> QED BY <3>a, <3>b
  <2> QED BY <2>sub, <2>sup
<1>dom. DOMAIN hta
          = {l \in Learners : \E y \in TranExclusive(x) : l \in Lrns(y)}
  BY <1>dom0, <1>lrnseq, <1>htdomeq, <1>domchar DEF HTLearners
\* ------------------------------------------------------------------ per-l
<1>main. \A l \in DOMAIN hta :
       /\ hta[l] = Digest(hta[l].id)
       /\ hta[l].id \in TranExclusive(x)
       /\ l \in Lrns(hta[l].id)
       /\ \A y \in TranExclusive(x) :
            l \in Lrns(y) => B(y) <= B(hta[l].id)
  <2> SUFFICES ASSUME NEW l \in DOMAIN hta
      PROVE /\ hta[l] = Digest(hta[l].id)
            /\ hta[l].id \in TranExclusive(x)
            /\ l \in Lrns(hta[l].id)
            /\ \A y \in TranExclusive(x) :
                 l \in Lrns(y) => B(y) <= B(hta[l].id)
    OBVIOUS
  <2> DEFINE C == HTCandidates(l, recs)
  <2>sD. l \in HTLearners(recs)  BY <1>dom0
  <2>ent. hta[l]
            = CHOOSE c \in HTCandidates(l, recs) :
                \A c2 \in HTCandidates(l, recs) : c.bal >= c2.bal
    BY <2>sD DEF HighestTwoAsAssemble
  <2>candR. \A p \in R : l \in Lrns(p) => Digest(p) \in C
    <3> SUFFICES ASSUME NEW p \in R, l \in Lrns(p)
        PROVE Digest(p) \in C  OBVIOUS
    <3>1. Digest(p) \in recs  OBVIOUS
    <3>2. l \in Digest(p).lrns  BY <1>idp
    <3>3. Digest(p) \in {y \in recs : l \in y.lrns}  BY <3>1, <3>2
    <3> QED BY <3>3 DEF HTCandidates
  <2>candC. \A p \in R : l \in DOMAIN DigestHighestTwoAs(p) =>
              DigestHighestTwoAs(p)[l] \in C
    <3> SUFFICES ASSUME NEW p \in R, l \in DOMAIN DigestHighestTwoAs(p)
        PROVE DigestHighestTwoAs(p)[l] \in C  OBVIOUS
    <3>1. Digest(p) \in recs  OBVIOUS
    <3>2. l \in DOMAIN Digest(p).highesttwoas  BY <1>idp
    <3>3. Digest(p) \in {y \in recs : l \in DOMAIN y.highesttwoas}
      BY <3>1, <3>2
    <3>4. HTCarrierCand(l, Digest(p)) = DigestHighestTwoAs(p)[l]
      BY <1>idp DEF HTCarrierCand
    <3> QED BY <3>3, <3>4 DEF HTCandidates
  <2>shape. \A c \in C : /\ c = Digest(c.id)
                         /\ c.id \in TranExclusive(x)
                         /\ l \in Lrns(c.id)
    <3> SUFFICES ASSUME NEW c \in C
        PROVE /\ c = Digest(c.id)
              /\ c.id \in TranExclusive(x)
              /\ l \in Lrns(c.id)
      OBVIOUS
    <3>split. \/ c \in {y \in recs : l \in y.lrns}
              \/ c \in {HTCarrierCand(l, rc) :
                          rc \in {y \in recs : l \in DOMAIN y.highesttwoas}}
      BY DEF HTCandidates
    <3>a. CASE c \in {y \in recs : l \in y.lrns}
      <4>1. PICK p \in R : c = Digest(p)  BY <3>a
      <4>2. l \in Digest(p).lrns  BY <3>a, <4>1
      <4>3. l \in Lrns(p)  BY <4>2, <1>idp
      <4>4. c.id = p  BY <4>1, <1>idp
      <4> QED BY <4>1, <4>3, <4>4, <1>pTE
    <3>b. CASE c \in {HTCarrierCand(l, rc) :
                        rc \in {y \in recs : l \in DOMAIN y.highesttwoas}}
      <4>rc. PICK rc \in {y \in recs : l \in DOMAIN y.highesttwoas} :
               c = HTCarrierCand(l, rc)
        BY <3>b
      <4>p. PICK p \in R : rc = Digest(p)  BY <4>rc
      <4>c2. c = DigestHighestTwoAs(p)[l] /\ l \in DOMAIN DigestHighestTwoAs(p)
        BY <4>rc, <4>p, <1>idp DEF HTCarrierCand
      <4>ihp. HighestTwoAsInvariant(p)  BY <1>ih
      <4>facts. /\ DigestHighestTwoAs(p)[l]
                     = Digest(DigestHighestTwoAs(p)[l].id)
                /\ DigestHighestTwoAs(p)[l].id \in TranExclusive(p)
                /\ l \in Lrns(DigestHighestTwoAs(p)[l].id)
        BY <4>ihp, <4>c2 DEF HighestTwoAsInvariant
      <4> QED BY <4>c2, <4>facts, <1>texPP
    <3> QED BY <3>split, <3>a, <3>b
  <2>balc. \A c \in C : c.bal = B(c.id) /\ c.bal \in Nat
    <3> SUFFICES ASSUME NEW c \in C
        PROVE c.bal = B(c.id) /\ c.bal \in Nat  OBVIOUS
    <3>1. c = Digest(c.id) /\ c.id \in TranExclusive(x)  BY <2>shape
    <3>2. c.id \in Messages  BY <3>1, <1>teM
    <3>3. DigestBal(c.id) = B(c.id)  BY <3>2, BalRec
    <3>4. c.bal = B(c.id)  BY <3>1, <3>3 DEF DigestBal
    <3>5. B(c.id) \in Ballots  BY <3>2, BBallot
    <3> QED BY <3>4, <3>5 DEF Ballots
  <2>ne. C # {}
    <3>1. \/ l \in UNION {rc.lrns : rc \in recs}
          \/ l \in UNION {DOMAIN rc.highesttwoas : rc \in recs}
      BY <2>sD DEF HTLearners
    <3>a. CASE l \in UNION {rc.lrns : rc \in recs}
      <4>1. l \in UNION {Lrns(p) : p \in R}  BY <3>a, <1>lrnseq
      <4>2. PICK p \in R : l \in Lrns(p)  BY <4>1
      <4> QED BY <4>2, <2>candR
    <3>b. CASE l \in UNION {DOMAIN rc.highesttwoas : rc \in recs}
      <4>1. l \in UNION {DOMAIN DigestHighestTwoAs(p) : p \in R}
        BY <3>b, <1>htdomeq
      <4>2. PICK p \in R : l \in DOMAIN DigestHighestTwoAs(p)  BY <4>1
      <4> QED BY <4>2, <2>candC
    <3> QED BY <3>1, <3>a, <3>b
  <2>fin. IsFiniteSet(C)
    <3>ftx. IsFiniteSet(Tran(x))  BY DEF TranFinite
    <3>fR. IsFiniteSet(R)
      <4>1. R \subseteq Tran(x)  BY <1>rsub DEF TranExclusive
      <4> QED BY <4>1, <3>ftx, FS_Subset
    <3>frecs. IsFiniteSet(recs)  BY <3>fR, FS_Image
    <3>f1. IsFiniteSet({y \in recs : l \in y.lrns})  BY <3>frecs, FS_Subset
    <3>f2. IsFiniteSet({y \in recs : l \in DOMAIN y.highesttwoas})
      BY <3>frecs, FS_Subset
    <3>fC. IsFiniteSet({HTCarrierCand(l, rc) :
                          rc \in {y \in recs : l \in DOMAIN y.highesttwoas}})
      BY <3>f2, FS_Image
    <3> QED BY <3>f1, <3>fC, FS_Union DEF HTCandidates
  <2>maxE. \E c \in C : \A c2 \in C : c.bal >= c2.bal
    <3>1. \A c \in C : c.bal \in Nat  BY <2>balc
    <3> QED BY <2>fin, <2>ne, <3>1, BalFldMaxExists
  <2>win. /\ hta[l] \in C
          /\ \A c2 \in C : hta[l].bal >= c2.bal
    BY <2>ent, <2>maxE
  <2>c123. /\ hta[l] = Digest(hta[l].id)
           /\ hta[l].id \in TranExclusive(x)
           /\ l \in Lrns(hta[l].id)
    BY <2>win, <2>shape
  <2>wbal. hta[l].bal = B(hta[l].id)
             /\ hta[l].bal \in Nat
    BY <2>win, <2>balc
  <2>hi. \A y \in TranExclusive(x) :
           l \in Lrns(y) => B(y) <= B(hta[l].id)
    <3> SUFFICES ASSUME NEW y \in TranExclusive(x), l \in Lrns(y)
        PROVE B(y) <= B(hta[l].id)
      OBVIOUS
    <3>p. PICK p \in R : y \in Tran(p)  BY <1>tex
    <3>ynat. B(y) \in Nat
      <4>1. y \in Messages  BY <1>teM
      <4>2. B(y) \in Ballots  BY <4>1, BBallot
      <4> QED BY <4>2 DEF Ballots
    <3>a. CASE y = p
      <4>c. Digest(p) \in C  BY <3>a, <2>candR
      <4>cb. Digest(p).bal = B(p)  BY <1>idp
      <4>le. hta[l].bal >= Digest(p).bal
        BY <4>c, <2>win
      <4> QED BY <3>a, <4>cb, <4>le, <2>wbal, <3>ynat, SMT
    <3>b. CASE y # p
      <4>yTE. y \in TranExclusive(p)  BY <3>p, <3>b DEF TranExclusive
      <4>ihp. HighestTwoAsInvariant(p)  BY <1>ih
      <4>ldom. l \in DOMAIN DigestHighestTwoAs(p)
        <5>1. l \in Learners  BY <1>dom
        <5> QED BY <5>1, <4>yTE, <1>ihdom
      <4>c. DigestHighestTwoAs(p)[l] \in C  BY <4>ldom, <2>candC
      <4>bound. B(y) <= B(DigestHighestTwoAs(p)[l].id)
        BY <4>ihp, <4>ldom, <4>yTE DEF HighestTwoAsInvariant
      <4>cb. DigestHighestTwoAs(p)[l].bal = B(DigestHighestTwoAs(p)[l].id)
               /\ DigestHighestTwoAs(p)[l].bal \in Nat
        BY <4>c, <2>balc
      <4>le. hta[l].bal >= DigestHighestTwoAs(p)[l].bal
        BY <4>c, <2>win
      <4> QED BY <4>bound, <4>cb, <4>le, <2>wbal, <3>ynat, SMT
    <3> QED BY <3>a, <3>b
  <2> QED BY <2>c123, <2>hi
<1> QED BY <1>dom, <1>main DEF HighestTwoAsCorrect
====================================================================
