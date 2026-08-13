----------------------------- MODULE IsOneBRec -----------------------------
\*   TranExclusiveRefs, TranSubMessages, BMonotone, BBallot,
\*   BAchievedByProposal -> cited lemmas
\*   FiniteSetTheorems -> FS_Subset, FS_Singleton, FS_AddElement
\*   TLAPS -> SMT; proof-only
EXTENDS MessageInterface, TranExclusiveRefs, TranSubMessages,
        BMonotone, BBallot, BAchievedByProposal, FiniteSetTheorems
LOCAL INSTANCE TLAPS

\* Refs-local characterization of IsOneB: m is a OneB exactly when some ref
\* is a proposal carrying m's ballot, and every OTHER ref of m -- and every
\* ref of that proposal -- has a strictly lower ballot. (B is monotone
\* along Tran, so bounding the refs bounds everything beneath them; the
\* count-2 set {z \in Tran(m) : B(z) = B(m)} is then exactly {m, p}.)
\* This lets a future memo field decide OneB-ness from refs' data alone,
\* instead of IsOneB's Cardinality-over-Tran definition.
LEMMA IsOneBRec ==
  ASSUME MessageInterfaceAssumptions, NEW m \in Messages
  PROVE IsOneB(m) <=>
    (/\ ~IsProposal(m)
     /\ \E p \in Refs(m) :
          /\ IsProposal(p)
          /\ B(p) = B(m)
          /\ \A y \in (Refs(m) \cup Refs(p)) \ {p} : B(y) < B(m))
<1>tok. TypeOKMessageInterface  BY DEF MessageInterfaceAssumptions
<1>tf. TranFinite  BY DEF MessageInterfaceAssumptions
<1>tt. TranTrans  BY DEF MessageInterfaceAssumptions
<1>ta. TranAcyclic  BY DEF MessageInterfaceAssumptions
<1>anp. AlwaysAProposal  BY DEF MessageInterfaceAssumptions
<1> DEFINE W == {z \in Tran(m) : B(z) = B(m)}
<1>tex. TranExclusive(m) = UNION {Tran(r) : r \in Refs(m)}
  BY <1>tok, <1>tf, <1>tt, <1>ta, TranExclusiveRefs
<1>rsub. Refs(m) \subseteq TranExclusive(m)  BY DEF Refs
<1>rM. Refs(m) \subseteq Messages
  BY <1>rsub, <1>tok, <1>tt, TranSubMessages DEF TranExclusive
<1>finW. IsFiniteSet(W)
  <2>1. W \subseteq Tran(m)  OBVIOUS
  <2>2. IsFiniteSet(Tran(m))  BY <1>tf DEF TranFinite
  <2> QED BY <2>1, <2>2, FS_Subset
<1>mW. m \in W
  <2>1. m \in Tran(m)  BY DEF Tran
  <2> QED BY <2>1
<1>mnat. B(m) \in Nat
  <2>1. B(m) \in Ballots  BY <1>tok, <1>tf, <1>anp, BBallot
  <2> QED BY <2>1 DEF Ballots
<1>tnat. \A z \in Tran(m) : B(z) \in Nat
  <2> SUFFICES ASSUME NEW z \in Tran(m) PROVE B(z) \in Nat  OBVIOUS
  <2>1. z \in Messages  BY <1>tok, <1>tt, TranSubMessages
  <2>2. B(z) \in Ballots  BY <2>1, <1>tok, <1>tf, <1>anp, BBallot
  <2> QED BY <2>2 DEF Ballots
\* Three distinct members of W contradict Cardinality(W) = 2.
<1>W3. ASSUME NEW u1, NEW u2, u1 \in W, u2 \in W,
              u1 # u2, u1 # m, u2 # m,
              Cardinality(W) = 2
       PROVE FALSE
  <2>1. IsFiniteSet({u1}) /\ Cardinality({u1}) = 1  BY FS_Singleton
  <2>2. u2 \notin {u1} /\ {u1, u2} = {u1} \cup {u2}  BY <1>W3
  <2>3. IsFiniteSet({u1, u2}) /\ Cardinality({u1, u2}) = 2
    BY <2>1, <2>2, FS_AddElement
  <2>4. m \notin {u1, u2} /\ {m, u1, u2} = {u1, u2} \cup {m}  BY <1>W3
  <2>5. Cardinality({m, u1, u2}) = 3  BY <2>3, <2>4, FS_AddElement
  <2>6. {m, u1, u2} \subseteq W  BY <1>W3, <1>mW
  <2>7. Cardinality({m, u1, u2}) <= Cardinality(W)
    BY <2>6, <1>finW, FS_Subset
  <2> QED BY <2>5, <2>7, <1>W3, SMT
\* ------------------------------------------------------------- forward
<1>fwd. IsOneB(m) =>
    (/\ ~IsProposal(m)
     /\ \E p \in Refs(m) :
          /\ IsProposal(p)
          /\ B(p) = B(m)
          /\ \A y \in (Refs(m) \cup Refs(p)) \ {p} : B(y) < B(m))
  <2>1. CASE IsOneB(m)
    <3>np. ~IsProposal(m) /\ Cardinality(W) = 2  BY <2>1 DEF IsOneB
    <3>ach. PICK q \in Tran(m) :
              IsProposal(q) /\ ProposalBal(q) = B(m) /\ B(q) = B(m)
      BY BAchievedByProposal
    <3>qm. q # m  BY <3>ach, <3>np
    <3>qTE. q \in TranExclusive(m)  BY <3>qm DEF TranExclusive
    <3>r. PICK r \in Refs(m) : q \in Tran(r)  BY <3>qTE, <1>tex
    <3>rM. r \in Messages  BY <1>rM
    <3>rT. r \in Tran(m)  BY <1>rsub DEF TranExclusive
    <3>rm. r # m  BY <1>rsub DEF TranExclusive
    <3>br. B(r) = B(m)
      <4>1. B(r) <= B(m)  BY <3>rT, <1>tok, <1>tt, <1>tf, <1>anp, BMonotone
      <4>2. B(q) <= B(r)
        BY <3>r, <3>rM, <1>tok, <1>tt, <1>tf, <1>anp, BMonotone
      <4>3. B(r) \in Nat  BY <3>rT, <1>tnat
      <4>4. B(q) \in Nat  BY <3>ach, <1>tnat
      <4> QED BY <3>ach, <4>1, <4>2, <4>3, <4>4, <1>mnat, SMT
    <3>rW. r \in W  BY <3>rT, <3>br
    <3>qW. q \in W  BY <3>ach
    <3>req. q = r
      <4>1. CASE q # r
        <5> QED BY <4>1, <3>qW, <3>rW, <3>qm, <3>rm, <3>np, <1>W3
      <4> QED BY <4>1
    <3>rprop. IsProposal(r) /\ B(r) = B(m)  BY <3>req, <3>ach, <3>br
    <3>others. \A y \in (Refs(m) \cup Refs(r)) \ {r} : B(y) < B(m)
      <4> SUFFICES ASSUME NEW y \in (Refs(m) \cup Refs(r)) \ {r}
          PROVE B(y) < B(m)
        OBVIOUS
      <4>yTE. y \in TranExclusive(m)
        <5>a. CASE y \in Refs(m)
          <6> QED BY <5>a, <1>rsub
        <5>b. CASE y \in Refs(r)
          <6>1. y \in TranExclusive(r)  BY <5>b DEF Refs
          <6>2. y \in Tran(r)  BY <6>1 DEF TranExclusive
          <6> QED BY <6>2, <3>r, <1>tex
        <5> QED BY <5>a, <5>b
      <4>ym. y # m  BY <4>yTE DEF TranExclusive
      <4>yr. y # r  OBVIOUS
      <4>yT. y \in Tran(m)  BY <4>yTE DEF TranExclusive
      <4>le. B(y) <= B(m)
        BY <4>yT, <1>tok, <1>tt, <1>tf, <1>anp, BMonotone
      <4>ne. B(y) # B(m)
        <5>1. CASE B(y) = B(m)
          <6>yW. y \in W  BY <4>yT, <5>1
          <6> QED BY <6>yW, <3>rW, <4>yr, <4>ym, <3>rm, <3>np, <1>W3
        <5> QED BY <5>1
      <4>tynat. B(y) \in Nat  BY <4>yT, <1>tnat
      <4> QED BY <4>le, <4>ne, <4>tynat, <1>mnat, SMT
    <3> QED BY <3>np, <3>r, <3>rprop, <3>others
  <2> QED BY <2>1
\* ------------------------------------------------------------ backward
<1>bwd. (/\ ~IsProposal(m)
         /\ \E p \in Refs(m) :
              /\ IsProposal(p)
              /\ B(p) = B(m)
              /\ \A y \in (Refs(m) \cup Refs(p)) \ {p} : B(y) < B(m))
        => IsOneB(m)
  <2>1. CASE /\ ~IsProposal(m)
             /\ \E p \in Refs(m) :
                  /\ IsProposal(p)
                  /\ B(p) = B(m)
                  /\ \A y \in (Refs(m) \cup Refs(p)) \ {p} : B(y) < B(m)
    <3>p. PICK p \in Refs(m) :
            /\ IsProposal(p)
            /\ B(p) = B(m)
            /\ \A y \in (Refs(m) \cup Refs(p)) \ {p} : B(y) < B(m)
      BY <2>1
    <3>pTE. p \in TranExclusive(m)  BY <1>rsub
    <3>pm. p # m  BY <3>pTE DEF TranExclusive
    <3>pM. p \in Messages  BY <1>rM
    <3>pT. p \in Tran(m)  BY <3>pTE DEF TranExclusive
    <3>pW. p \in W  BY <3>pT, <3>p
    <3>texp. TranExclusive(p) = UNION {Tran(rr) : rr \in Refs(p)}
      BY <3>pM, <1>tok, <1>tf, <1>tt, <1>ta, TranExclusiveRefs
    <3>sub. W \subseteq {m, p}
      <4> SUFFICES ASSUME NEW z \in W, z # m, z # p PROVE FALSE
        OBVIOUS
      <4>zT. z \in Tran(m) /\ B(z) = B(m)  OBVIOUS
      <4>zTE. z \in TranExclusive(m)  BY <4>zT DEF TranExclusive
      <4>znat. B(z) \in Nat  BY <4>zT, <1>tnat
      <4>r. PICK r \in Refs(m) : z \in Tran(r)  BY <4>zTE, <1>tex
      <4>rM. r \in Messages  BY <1>rM
      <4>a. CASE r = p
        <5>1. z \in Tran(p)  BY <4>r, <4>a
        <5>2. z \in TranExclusive(p)  BY <5>1 DEF TranExclusive
        <5>3. PICK rr \in Refs(p) : z \in Tran(rr)  BY <5>2, <3>texp
        <5>rrTE. rr \in TranExclusive(p)  BY <5>3 DEF Refs
        <5>rrM. rr \in Messages
          BY <5>rrTE, <3>pM, <1>tok, <1>tt, TranSubMessages
            DEF TranExclusive
        <5>rrp. rr # p  BY <5>rrTE DEF TranExclusive
        <5>4. rr \in (Refs(m) \cup Refs(p)) \ {p}  BY <5>3, <5>rrp
        <5>5. B(rr) < B(m)  BY <5>4, <3>p
        <5>6. B(z) <= B(rr)
          BY <5>3, <5>rrM, <1>tok, <1>tt, <1>tf, <1>anp, BMonotone
        <5>7. B(rr) \in Nat
          <6>1. B(rr) \in Ballots
            BY <5>rrM, <1>tok, <1>tf, <1>anp, BBallot
          <6> QED BY <6>1 DEF Ballots
        <5> QED BY <4>zT, <5>5, <5>6, <5>7, <4>znat, <1>mnat, SMT
      <4>b. CASE r # p
        <5>1. r \in (Refs(m) \cup Refs(p)) \ {p}  BY <4>r, <4>b
        <5>2. B(r) < B(m)  BY <5>1, <3>p
        <5>3. B(z) <= B(r)
          BY <4>r, <4>rM, <1>tok, <1>tt, <1>tf, <1>anp, BMonotone
        <5>4. B(r) \in Nat
          <6>1. r \in Tran(m)  BY <1>rsub DEF TranExclusive
          <6> QED BY <6>1, <1>tnat
        <5> QED BY <4>zT, <5>2, <5>3, <5>4, <4>znat, <1>mnat, SMT
      <4> QED BY <4>a, <4>b
    <3>eq. W = {m, p}  BY <3>sub, <1>mW, <3>pW
    <3>card. Cardinality(W) = 2
      <4>1. IsFiniteSet({p}) /\ Cardinality({p}) = 1  BY FS_Singleton
      <4>2. m \notin {p}  BY <3>pm
      <4>3. {m, p} = {p} \cup {m}  OBVIOUS
      <4> QED BY <4>1, <4>2, <4>3, <3>eq, FS_AddElement
    <3> QED BY <2>1, <3>card DEF IsOneB
  <2> QED BY <2>1
<1> QED BY <1>fwd, <1>bwd
====================================================================
