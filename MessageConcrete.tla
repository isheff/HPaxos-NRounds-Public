------------------------- MODULE MessageConcrete -------------------------
\* A concrete Messages construction, generic over ValueInterface and
\* LearnerGraphInterface (their record CONSTANTs are left abstract), proving
\* MessageInterfaceAssumptions for the resulting instantiation of
\* MessageInterface.  The construction is extremely close to HPaxos.tla's
\* Message (not MessageCandidate): a level-indexed fixpoint of records
\* [sender, payload, priors] filtered down by a WellFormed predicate.  Most
\* of the "Interface-land" macros (Tran, Refs, Sig, B, V, HasDepth, Fresh,
\* Qd, Lrns, Caught, Con, ...) are necessarily duplicated here in
\* "Concrete-land" form, operating directly on the record structure instead
\* of through the abstract MessageInterface record's raw fields.
EXTENDS MessageInterface
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE FiniteSetsExt
LOCAL INSTANCE FiniteSetTheorems
LOCAL INSTANCE NaturalsInduction

\* ---- the concrete model: message candidates (mirrors HPaxos.tla) ----
\* Senders is Acceptors plus one extra "proposer" identity, guaranteed
\* distinct from every acceptor (via a Russell's-paradox-style existence
\* argument: no set can contain everything).  AlwaysANewProposal has no
\* sender-related side condition, but WellFormed's "an acceptor may not
\* catch itself" clause means a freshly-constructed proposal cannot safely
\* be attributed to an arbitrary (possibly already-caught) acceptor; the
\* extra non-acceptor identity sidesteps that clause entirely, with no need
\* for a third abstract CONSTANT (stays generic over ValueInterface and
\* LearnerGraphInterface only, per the original brief).
LEMMA CExistsOutsideAcceptors == \E x : x \notin Acceptors
<1> SUFFICES ASSUME \A x : x \in Acceptors
             PROVE FALSE
  OBVIOUS
<1>univ. \A x : x \in Acceptors  OBVIOUS
<1> DEFINE R == {y \in Acceptors : y \notin y}
<1>1. R \in Acceptors  BY <1>univ
<1>2. R \in R <=> (R \in Acceptors /\ R \notin R)  OBVIOUS
<1> QED BY <1>1, <1>2

CProposerSender == CHOOSE x : x \notin Acceptors

LEMMA CProposerSenderNotAcceptor == CProposerSender \notin Acceptors
BY CExistsOutsideAcceptors DEF CProposerSender

CSenders == Acceptors \cup {CProposerSender}
CProposal == {[type |-> "proposal", ballot |-> b] : b \in Ballots}
CReply == {[type |-> "reply"]}
CPayload == CProposal \cup CReply

CMCLBase == {[sender |-> r[1], payload |-> r[2], priors |-> {}] : r \in CSenders \X CPayload}
CMCLNew(prev) ==
  {[sender |-> r[1], payload |-> r[2], priors |-> r[3]] :
   r \in CSenders \X CPayload \X {x \in SUBSET prev : IsFiniteSet(x)}}
CMCLExt(prev) == prev \cup CMCLNew(prev)
CMCAL[l \in Nat] == IF l = 0 THEN CMCLBase ELSE CMCLExt(CMCAL[l-1])
CMC == UNION {CMCAL[l] : l \in Nat}
CMinLevel(m) == Min({l \in Nat : m \in CMCAL[l]})

\* --- basic shape / monotonicity ---
LEMMA CMCALUnfold ==
  \A l \in Nat : CMCAL[l] = IF l = 0 THEN CMCLBase ELSE CMCLExt(CMCAL[l-1])
<1> DEFINE Def(g, j) == IF j = 0 THEN CMCLBase ELSE CMCLExt(g[j-1])
<1> DEFINE mcl[j \in Nat] == Def(mcl, j)
<1>m1. ASSUME NEW j \in Nat, NEW g, NEW h, \A i \in 0..(j-1) : g[i] = h[i]
       PROVE  Def(g, j) = Def(h, j)
  <2>1. CASE j = 0  BY <2>1
  <2>2. CASE j # 0
    <3>1. g[j-1] = h[j-1]  BY <1>m1, <2>2
    <3> QED BY <3>1, <2>2
  <2> QED BY <2>1, <2>2
<1> HIDE DEF Def
<1>m2. mcl = [j \in Nat |-> Def(mcl, j)]  BY <1>m1, RecursiveFcnOfNat, Isa
<1>m3. mcl = CMCAL  BY Zenon DEF CMCAL, Def
<1>4. CMCAL = [j \in Nat |-> Def(CMCAL, j)]  BY <1>m2, <1>m3
<1> QED BY <1>4 DEF Def

LEMMA CMCALMono ==
  ASSUME NEW l \in Nat
  PROVE CMCAL[l] \subseteq CMCAL[l+1]
<1>1. l + 1 # 0  OBVIOUS
<1>2. (l+1) - 1 = l  OBVIOUS
<1>3. CMCAL[l+1] = CMCLExt(CMCAL[(l+1)-1])  BY <1>1, CMCALUnfold
<1>4. CMCAL[l+1] = CMCLExt(CMCAL[l])  BY <1>2, <1>3
<1> QED BY <1>4 DEF CMCLExt

LEMMA CMinLevelDom ==
  ASSUME NEW z \in CMC
  PROVE /\ CMinLevel(z) \in Nat
        /\ z \in CMCAL[CMinLevel(z)]
        /\ \A k \in Nat : z \in CMCAL[k] => CMinLevel(z) <= k
<1> DEFINE LS == {l \in Nat : z \in CMCAL[l]}
<1> DEFINE P(k) == z \in CMCAL[k]
<1>a. PICK n \in Nat : P(n)  BY DEF CMC
<1>2. \E m \in Nat : P(m) /\ \A k \in 0..m-1 : ~P(k)
  <2> HIDE DEF P
  <2> QED BY <1>a, SmallestNatural
<1>3. \E x \in LS : \A y \in LS : x =< y
  <2>1. PICK m \in Nat : P(m) /\ \A k \in 0..m-1 : ~P(k)  BY <1>2
  <2>2. m \in LS  BY <2>1
  <2>3. \A y \in LS : m =< y
    <3>1. ASSUME NEW y \in LS PROVE m =< y  BY <2>1, <3>1
    <3> QED BY <3>1
  <2> QED BY <2>2, <2>3
<1>4. CMinLevel(z) \in LS /\ (\A y \in LS : CMinLevel(z) =< y)
  BY <1>3 DEF CMinLevel, Min
<1> QED
  <2>1. CMinLevel(z) \in Nat /\ z \in CMCAL[CMinLevel(z)]  BY <1>4
  <2>2. \A k \in Nat : z \in CMCAL[k] => CMinLevel(z) <= k
    <3>1. ASSUME NEW k \in Nat, z \in CMCAL[k] PROVE CMinLevel(z) <= k
      <4>1. k \in LS  BY <3>1
      <4> QED BY <1>4, <4>1
    <3> QED BY <3>1
  <2> QED BY <2>1, <2>2

LEMMA CMCALMonoGen ==
  ASSUME NEW k \in Nat, NEW l \in Nat, k <= l
  PROVE CMCAL[k] \subseteq CMCAL[l]
<1> DEFINE Q(n) == \A kk \in Nat : kk <= n => CMCAL[kk] \subseteq CMCAL[n]
<1>base. Q(0)
  <2> QED BY DEF Q
<1>step. \A n \in Nat : Q(n) => Q(n+1)
  <2> SUFFICES ASSUME NEW n \in Nat, Q(n), NEW kk \in Nat, kk <= n+1
               PROVE CMCAL[kk] \subseteq CMCAL[n+1]
    BY DEF Q
  <2>1. CASE kk = n+1
    <3> QED BY <2>1
  <2>2. CASE kk <= n
    <3>1. CMCAL[kk] \subseteq CMCAL[n]  BY <2>2 DEF Q
    <3>2. CMCAL[n] \subseteq CMCAL[n+1]  BY CMCALMono
    <3> QED BY <3>1, <3>2
  <2> QED BY <2>1, <2>2
<1>allQ. \A n \in Nat : Q(n)  BY <1>base, <1>step, NatInduction
<1> QED BY <1>allQ DEF Q
LEMMA CMCALMonoMem ==
  ASSUME NEW k \in Nat, NEW l \in Nat, k <= l, NEW z \in CMCAL[k]
  PROVE z \in CMCAL[l]
BY CMCALMonoGen

CGFun(F(_,_), R(_)) == CHOOSE g : g = [l \in Nat |->
    [x \in CMCAL[l] |->
       F(x, IF l = 0 THEN {} ELSE {g[l-1][y] : y \in R(x)})]]

CRecursiveFunc(F(_,_), R(_), m) ==
  LET g[l \in Nat] == [x \in CMCAL[l] |->
         F(x, IF l=0 THEN {} ELSE {g[l-1][y] : y \in R(x)})
      ]
   IN g[CMinLevel(m)][m]

LEMMA CRMFViaG ==
  ASSUME NEW F(_,_), NEW R(_), NEW z
  PROVE  CRecursiveFunc(F, R, z) = CGFun(F, R)[CMinLevel(z)][z]
BY DEF CRecursiveFunc, CGFun

LEMMA CGStep ==
  ASSUME NEW F(_,_), NEW R(_), NEW l \in Nat, NEW x \in CMCAL[l]
  PROVE  CGFun(F, R)[l][x] =
           F(x, IF l = 0 THEN {} ELSE {CGFun(F, R)[l-1][y] : y \in R(x)})
<1> DEFINE Def(g, k) == [z \in CMCAL[k] |->
                          F(z, IF k = 0 THEN {} ELSE {g[k-1][w] : w \in R(z)})]
<1> DEFINE gg[k \in Nat] == Def(gg, k)
<1>1. ASSUME NEW k \in Nat, NEW g, NEW h, \A i \in 0..(k-1) : g[i] = h[i]
      PROVE  Def(g, k) = Def(h, k)
  BY <1>1
<1> HIDE DEF Def
<1>2. gg = [k \in Nat |-> Def(gg, k)]  BY <1>1, RecursiveFcnOfNat, Isa
<1>3. gg = CGFun(F, R)  BY Zenon DEF CGFun, Def
<1>4. CGFun(F, R) = [k \in Nat |-> Def(CGFun(F, R), k)]  BY <1>2, <1>3
<1>5. CGFun(F, R)[l] = Def(CGFun(F, R), l)  BY <1>4
<1> QED  BY <1>5 DEF Def

CGRec(g, F(_,_), R(_)) ==
  \A l \in Nat : \A x \in CMCAL[l] :
    g[l][x] = F(x, IF l = 0 THEN {} ELSE {g[l-1][y] : y \in R(x)})

CQPred(g, n) == \A x \in CMCAL[n] :
                 g[n][x] = g[CMinLevel(x)][x]

LEMMA CLevelIndepGen ==
  ASSUME NEW g, NEW F(_,_), NEW R(_),
         CGRec(g, F, R),
         \A w \in CMC : R(w) \subseteq CMC,
         \A w \in CMC : \A y \in R(w) :
             CMinLevel(y) < CMinLevel(w),
         NEW ll \in Nat, NEW xx \in CMCAL[ll]
  PROVE  g[ll][xx] = g[CMinLevel(xx)][xx]
<1> DEFINE lev(z) == CMinLevel(z)
<1> DEFINE Q(n) == CQPred(g, n)
<1> SUFFICES \A n \in Nat : Q(n)
  BY DEF Q, CQPred
<1> HIDE DEF Q
<1>ind. \A n \in Nat : (\A mm \in 0..(n-1) : Q(mm)) => Q(n)
  <2> USE DEF Q, CQPred
  <2> SUFFICES ASSUME NEW n \in Nat, \A mm \in 0..(n-1) : Q(mm)
               PROVE  Q(n)
    OBVIOUS
  <2> SUFFICES ASSUME NEW x \in CMCAL[n]
               PROVE  g[n][x] = g[lev(x)][x]
    OBVIOUS
  <2>mc. x \in CMC  BY DEF CMC
  <2>lev. lev(x) \in Nat /\ x \in CMCAL[lev(x)] /\ lev(x) <= n
    BY <2>mc, CMinLevelDom
  <2>gn. g[n][x] = F(x, IF n = 0 THEN {} ELSE {g[n-1][y] : y \in R(x)})
    BY DEF CGRec
  <2>gl. g[lev(x)][x] = F(x, IF lev(x) = 0 THEN {} ELSE {g[lev(x)-1][y] : y \in R(x)})
    BY <2>lev DEF CGRec
  <2> SUFFICES (IF n = 0 THEN {} ELSE {g[n-1][y] : y \in R(x)})
             = (IF lev(x) = 0 THEN {} ELSE {g[lev(x)-1][y] : y \in R(x)})
    BY <2>gn, <2>gl
  <2>R. \A y \in R(x) : y \in CMC /\ lev(y) \in Nat /\ lev(y) < lev(x)
    <3>1. ASSUME NEW y \in R(x)
          PROVE  y \in CMC /\ lev(y) \in Nat /\ lev(y) < lev(x)
      <4>1. y \in CMC   BY <2>mc
      <4>2. lev(y) \in Nat           BY <4>1, CMinLevelDom
      <4>3. lev(y) < lev(x)          BY <2>mc
      <4> QED BY <4>1, <4>2, <4>3
    <3> QED BY <3>1
  <2>1. CASE n = 0
    <3>1. lev(x) = 0   BY <2>1, <2>lev
    <3> QED BY <2>1, <3>1
  <2>2. CASE n # 0 /\ lev(x) = 0
    <3>1. R(x) = {}    BY <2>2, <2>R
    <3> QED BY <2>2, <3>1
  <2>3. CASE n # 0 /\ lev(x) # 0
    <3>0. /\ n-1 \in Nat /\ lev(x)-1 \in Nat
          /\ n-1 \in 0..(n-1) /\ lev(x)-1 \in 0..(n-1)
      BY <2>3, <2>lev
    <3>1. {g[n-1][y] : y \in R(x)} = {g[lev(x)-1][y] : y \in R(x)}
      <4>1. ASSUME NEW y \in R(x) PROVE g[n-1][y] = g[lev(x)-1][y]
        <5>1. y \in CMC /\ lev(y) \in Nat /\ lev(y) < lev(x)   BY <2>R
        <5>2. y \in CMCAL[lev(y)]   BY <5>1, CMinLevelDom
        <5>3. lev(y) <= n-1 /\ lev(y) <= lev(x)-1     BY <5>1, <2>3, <2>lev, <3>0
        <5>4. y \in CMCAL[n-1]      BY <5>1, <5>2, <5>3, <3>0, CMCALMonoMem
        <5>5. y \in CMCAL[lev(x)-1] BY <5>1, <5>2, <5>3, <3>0, CMCALMonoMem
        <5>8. g[n-1][y] = g[lev(y)][y]                BY <3>0, <5>4
        <5>9. g[lev(x)-1][y] = g[lev(y)][y]           BY <3>0, <5>5
        <5> QED BY <5>8, <5>9
      <4> QED BY <4>1
    <3> QED BY <2>3, <3>1
  <2> QED BY <2>1, <2>2, <2>3
<1> QED BY <1>ind, GeneralNatInduction, IsaM("blast")

LEMMA CLevelIndep ==
  ASSUME NEW F(_,_), NEW R(_),
         \A w \in CMC : R(w) \subseteq CMC,
         \A w \in CMC : \A y \in R(w) :
             CMinLevel(y) < CMinLevel(w),
         NEW l \in Nat, NEW x \in CMCAL[l]
  PROVE  CGFun(F, R)[l][x] = CGFun(F, R)[CMinLevel(x)][x]
<1>1. CGRec(CGFun(F, R), F, R)  BY CGStep DEF CGRec
<1> QED BY <1>1, CLevelIndepGen

LEMMA CRecursiveFuncRec ==
  ASSUME NEW F(_,_),
         NEW R(_),
         NEW m \in CMC,
         \A x \in CMC : R(x) \subseteq CMC,
         \A x \in CMC : \A y \in R(x) :
             CMinLevel(y) < CMinLevel(x)
  PROVE CRecursiveFunc(F, R, m) =
    F(m, {CRecursiveFunc(F, R, p): p \in R(m)})
<1> DEFINE g == CGFun(F, R)
<1> DEFINE lev(z) == CMinLevel(z)
<1>dom. lev(m) \in Nat /\ m \in CMCAL[lev(m)]
  BY CMinLevelDom
<1>sub. ASSUME NEW p \in R(m)
        PROVE  /\ p \in CMC
               /\ lev(p) \in Nat
               /\ lev(p) < lev(m)
  <2>1. p \in CMC  BY <1>dom
  <2>2. lev(p) \in Nat          BY <2>1, CMinLevelDom
  <2>3. lev(p) < lev(m)         BY <1>dom, <2>1
  <2> QED BY <2>1, <2>2, <2>3
<1>1. CRecursiveFunc(F, R, m) = g[lev(m)][m]
  BY CRMFViaG
<1>2. g[lev(m)][m] = F(m, IF lev(m) = 0 THEN {} ELSE {g[lev(m)-1][y] : y \in R(m)})
  BY <1>dom, CGStep
<1> SUFFICES (IF lev(m) = 0 THEN {} ELSE {g[lev(m)-1][y] : y \in R(m)})
             = {CRecursiveFunc(F, R, p) : p \in R(m)}
  BY <1>1, <1>2
<1>3. CASE lev(m) = 0
  <2>1. R(m) = {}
    BY <1>3, <1>sub
  <2> QED BY <1>3, <2>1
<1>4. CASE lev(m) # 0
  <2>0. lev(m) - 1 \in Nat /\ lev(m) - 1 < lev(m)  BY <1>dom, <1>4
  <2>1. {g[lev(m)-1][y] : y \in R(m)} = {CRecursiveFunc(F, R, p) : p \in R(m)}
    <3>1. ASSUME NEW y \in R(m)
          PROVE  g[lev(m)-1][y] = CRecursiveFunc(F, R, y)
      <4>1. y \in CMC /\ lev(y) \in Nat /\ lev(y) < lev(m)  BY <1>sub
      <4>2. y \in CMCAL[lev(y)]                        BY <4>1, CMinLevelDom
      <4>3. lev(y) <= lev(m) - 1                                         BY <4>1, <2>0, <1>dom
      <4>4. y \in CMCAL[lev(m)-1]
        BY <4>1, <4>2, <4>3, <2>0, CMCALMonoMem
      <4>5. g[lev(m)-1][y] = g[lev(y)][y]                                BY <2>0, <4>4, CLevelIndep
      <4>6. CRecursiveFunc(F, R, y) = g[lev(y)][y]                 BY CRMFViaG
      <4> QED BY <4>5, <4>6
    <3> QED BY <3>1
  <2> QED BY <1>4, <2>1
<1> QED BY <1>3, <1>4

CTranR(m, tran_rec_priors) == {m} \cup UNION tran_rec_priors
CPriors(m) == m.priors

LEMMA CPriorsDecreasesLevel ==
  ASSUME NEW x \in CMC,
         NEW y \in CPriors(x)
  PROVE CMinLevel(y) < CMinLevel(x)
<1> DEFINE lx == CMinLevel(x)
<1>1. lx \in Nat /\ x \in CMCAL[lx]
      /\ \A kk \in Nat : x \in CMCAL[kk] => lx <= kk
  BY CMinLevelDom
<1>2. y \in x.priors  BY DEF CPriors
<1>3. lx # 0
  <2> SUFFICES ASSUME lx = 0 PROVE FALSE  OBVIOUS
  <2>1. x \in CMCLBase  BY <1>1, CMCALUnfold
  <2>2. x.priors = {}  BY <2>1 DEF CMCLBase
  <2> QED BY <1>2, <2>2
<1>4. lx - 1 \in Nat  BY <1>1, <1>3
<1>5. x \in CMCLExt(CMCAL[lx-1])  BY <1>1, <1>3, CMCALUnfold
<1>6. x \notin CMCAL[lx-1]
  <2> SUFFICES ASSUME x \in CMCAL[lx-1] PROVE FALSE  OBVIOUS
  <2>1. lx <= lx - 1  BY <1>1, <1>4
  <2> QED BY <2>1, <1>1, <1>3
<1>7. x \in CMCLNew(CMCAL[lx-1])  BY <1>5, <1>6 DEF CMCLExt
<1>8. x.priors \subseteq CMCAL[lx-1]
  <2>1. x.priors \in {x2 \in SUBSET CMCAL[lx-1] : IsFiniteSet(x2)}
    BY <1>7 DEF CMCLNew
  <2> QED BY <2>1
<1>9. y \in CMCAL[lx-1]  BY <1>2, <1>8
<1>10. y \in CMC  BY <1>4, <1>9 DEF CMC
<1>11. CMinLevel(y) <= lx - 1  BY <1>4, <1>9, <1>10, CMinLevelDom
<1>12. CMinLevel(y) \in Nat  BY <1>10, CMinLevelDom
<1> QED BY <1>11, <1>12, <1>1, <1>3, <1>4

CTran(m) == CRecursiveFunc(CTranR, CPriors, m)
CTranExcl(m) == {x \in CTran(m) : x # m}

LEMMA CPriorsInMC == \A w \in CMC : CPriors(w) \subseteq CMC
<1> SUFFICES ASSUME NEW w \in CMC PROVE CPriors(w) \subseteq CMC  OBVIOUS
<1> DEFINE lw == CMinLevel(w)
<1>1. lw \in Nat /\ w \in CMCAL[lw]
      /\ \A kk \in Nat : w \in CMCAL[kk] => lw <= kk  BY CMinLevelDom
<1>2. CASE lw = 0
  <2>1. w \in CMCLBase  BY <1>1, <1>2, CMCALUnfold
  <2>2. w.priors = {}  BY <2>1 DEF CMCLBase
  <2> QED BY <2>2 DEF CPriors
<1>3. CASE lw # 0
  <2>1. lw - 1 \in Nat  BY <1>1, <1>3
  <2>2. w \in CMCLExt(CMCAL[lw-1])  BY <1>1, <1>3, CMCALUnfold
  <2>3. w \notin CMCAL[lw-1]
    <3> SUFFICES ASSUME w \in CMCAL[lw-1] PROVE FALSE  OBVIOUS
    <3>1. lw <= lw - 1  BY <1>1, <2>1
    <3> QED BY <3>1, <1>1, <1>3
  <2>4. w \in CMCLNew(CMCAL[lw-1])  BY <2>2, <2>3 DEF CMCLExt
  <2>5. w.priors \in {x2 \in SUBSET CMCAL[lw-1] : IsFiniteSet(x2)}  BY <2>4 DEF CMCLNew
  <2>6. w.priors \subseteq CMCAL[lw-1]  BY <2>5
  <2>7. CMCAL[lw-1] \subseteq CMC  BY <2>1 DEF CMC
  <2> QED BY <2>6, <2>7 DEF CPriors
<1> QED BY <1>2, <1>3

LEMMA CTranRec == ASSUME NEW m \in CMC
  PROVE CTran(m) = {m} \cup UNION {CTran(p) : p \in CPriors(m)}
<1>1. \A xx \in CMC : CPriors(xx) \subseteq CMC  BY CPriorsInMC
<1>2. \A xx \in CMC : \A yy \in CPriors(xx) : CMinLevel(yy) < CMinLevel(xx)
  BY CPriorsDecreasesLevel
<1>3. CRecursiveFunc(CTranR, CPriors, m)
        = CTranR(m, {CRecursiveFunc(CTranR, CPriors, p) : p \in CPriors(m)})
  BY <1>1, <1>2, CRecursiveFuncRec
<1> QED BY <1>3 DEF CTran, CTranR

CTranBelowProp(x) == \A y \in CTran(x) :
                      y \in CMC /\ CMinLevel(y) <= CMinLevel(x)
LEMMA CTranLevelLE == \A x \in CMC : CTranBelowProp(x)
<1> DEFINE lev(z) == CMinLevel(z)
<1> DEFINE Q(n) == \A x \in CMC : lev(x) = n => CTranBelowProp(x)
<1> SUFFICES \A n \in Nat : Q(n)  BY CMinLevelDom DEF Q
<1> HIDE DEF Q
<1>ind. \A n \in Nat : (\A mm \in 0..(n-1) : Q(mm)) => Q(n)
  <2> USE DEF Q, CTranBelowProp
  <2> SUFFICES ASSUME NEW n \in Nat, \A mm \in 0..(n-1) : Q(mm),
                      NEW x \in CMC, lev(x) = n, NEW y \in CTran(x)
               PROVE  y \in CMC /\ lev(y) <= lev(x)
    OBVIOUS
  <2>1. CTran(x) = {x} \cup UNION {CTran(p) : p \in CPriors(x)}  BY CTranRec
  <2>2. CASE y = x  BY <2>2
  <2>3. CASE y # x
    <3>1. y \in UNION {CTran(p) : p \in CPriors(x)}  BY <2>1, <2>3
    <3>2. PICK p \in CPriors(x) : y \in CTran(p)  BY <3>1
    <3>3. p \in CMC  BY <3>2, CPriorsInMC
    <3>4. lev(p) < lev(x)  BY <3>2, CPriorsDecreasesLevel
    <3>5. lev(p) \in Nat  BY <3>3, CMinLevelDom
    <3>6. lev(p) \in 0..(n-1)  BY <3>4, <3>5
    <3>7. \A yy \in CTran(p) : yy \in CMC /\ lev(yy) <= lev(p)  BY <3>3, <3>6
    <3>8. y \in CMC /\ lev(y) <= lev(p)  BY <3>2, <3>7
    <3>9. lev(y) \in Nat  BY <3>8, CMinLevelDom
    <3> QED BY <3>8, <3>4, <3>5, <3>9
  <2> QED BY <2>2, <2>3
<1> QED BY <1>ind, GeneralNatInduction, IsaM("blast")

LEMMA CTranExclDecreasesLevel ==
  ASSUME NEW x \in CMC,
         NEW y \in CTranExcl(x)
  PROVE CMinLevel(y) < CMinLevel(x)
<1>1. y \in CTran(x) /\ y # x  BY DEF CTranExcl
<1>2. CTran(x) = {x} \cup UNION {CTran(p) : p \in CPriors(x)}  BY CTranRec
<1>3. y \in UNION {CTran(p) : p \in CPriors(x)}  BY <1>1, <1>2
<1>4. PICK p \in CPriors(x) : y \in CTran(p)  BY <1>3
<1>5. p \in CMC  BY <1>4, CPriorsInMC
<1>6. CMinLevel(p) < CMinLevel(x)  BY <1>4, CPriorsDecreasesLevel
<1>7. \A yy \in CTran(p) : yy \in CMC /\ CMinLevel(yy) <= CMinLevel(p)
  BY <1>5, CTranLevelLE DEF CTranBelowProp
<1>8. y \in CMC /\ CMinLevel(y) <= CMinLevel(p)  BY <1>4, <1>7
<1>9. CMinLevel(p) \in Nat  BY <1>5, CMinLevelDom
<1>10. CMinLevel(y) \in Nat  BY <1>8, CMinLevelDom
<1>11. CMinLevel(x) \in Nat  BY CMinLevelDom
<1> QED BY <1>6, <1>8, <1>9, <1>10, <1>11

LEMMA CPriorsFinite == \A w \in CMC : IsFiniteSet(CPriors(w))
<1> SUFFICES ASSUME NEW w \in CMC PROVE IsFiniteSet(CPriors(w))  OBVIOUS
<1> DEFINE lw == CMinLevel(w)
<1>1. lw \in Nat /\ w \in CMCAL[lw]
      /\ \A kk \in Nat : w \in CMCAL[kk] => lw <= kk  BY CMinLevelDom
<1>2. CASE lw = 0
  <2>1. w \in CMCLBase  BY <1>1, <1>2, CMCALUnfold
  <2>2. w.priors = {}  BY <2>1 DEF CMCLBase
  <2> QED BY <2>2, FS_EmptySet DEF CPriors
<1>3. CASE lw # 0
  <2>1. lw - 1 \in Nat  BY <1>1, <1>3
  <2>2. w \in CMCLExt(CMCAL[lw-1])  BY <1>1, <1>3, CMCALUnfold
  <2>3. w \notin CMCAL[lw-1]
    <3> SUFFICES ASSUME w \in CMCAL[lw-1] PROVE FALSE  OBVIOUS
    <3>1. lw <= lw - 1  BY <1>1, <2>1
    <3> QED BY <3>1, <1>1, <1>3
  <2>4. w \in CMCLNew(CMCAL[lw-1])  BY <2>2, <2>3 DEF CMCLExt
  <2>5. w.priors \in {x2 \in SUBSET CMCAL[lw-1] : IsFiniteSet(x2)}  BY <2>4 DEF CMCLNew
  <2> QED BY <2>5 DEF CPriors
<1> QED BY <1>2, <1>3

LEMMA CFiniteTran ==
  ASSUME NEW m \in CMC
  PROVE IsFiniteSet(CTran(m))
<1> DEFINE lev(z) == CMinLevel(z)
<1> DEFINE Q(n) == \A x \in CMC : lev(x) = n => IsFiniteSet(CTran(x))
<1> SUFFICES \A n \in Nat : Q(n)  BY CMinLevelDom DEF Q
<1> HIDE DEF Q
<1>ind. \A n \in Nat : (\A mm \in 0..(n-1) : Q(mm)) => Q(n)
  <2> USE DEF Q
  <2> SUFFICES ASSUME NEW n \in Nat, \A mm \in 0..(n-1) : Q(mm),
                      NEW x \in CMC, lev(x) = n
               PROVE  IsFiniteSet(CTran(x))
    OBVIOUS
  <2>1. CTran(x) = {x} \cup UNION {CTran(p) : p \in CPriors(x)}  BY CTranRec
  <2>2. IsFiniteSet({x})  BY FS_Singleton
  <2>3. IsFiniteSet(CPriors(x))  BY CPriorsFinite
  <2>4. IsFiniteSet({CTran(p) : p \in CPriors(x)})  BY <2>3, FS_Image
  <2>5. \A T \in {CTran(p) : p \in CPriors(x)} : IsFiniteSet(T)
    <3>1. ASSUME NEW T \in {CTran(p) : p \in CPriors(x)} PROVE IsFiniteSet(T)
      <4>1. PICK p \in CPriors(x) : T = CTran(p)  BY <3>1
      <4>2. p \in CMC  BY CPriorsInMC
      <4>3. lev(p) < lev(x)  BY CPriorsDecreasesLevel
      <4>4. lev(p) \in Nat  BY <4>2, CMinLevelDom
      <4>5. lev(p) \in 0..(n-1)  BY <4>3, <4>4
      <4>6. IsFiniteSet(CTran(p))  BY <4>2, <4>5
      <4> QED BY <4>1, <4>6
    <3> QED BY <3>1
  <2>6. IsFiniteSet(UNION {CTran(p) : p \in CPriors(x)})  BY <2>4, <2>5, FS_UNION
  <2> QED BY <2>1, <2>2, <2>6, FS_Union
<1> QED BY <1>ind, GeneralNatInduction, IsaM("blast")

LEMMA CMCAcyclic ==
  ASSUME NEW m \in CMC, NEW p \in CTranExcl(m)
  PROVE  ~(m \in CTran(p))
<1>1. CMinLevel(p) < CMinLevel(m)  BY CTranExclDecreasesLevel
<1>2. p \in CMC
  <2>1. p \in CTran(m)  BY DEF CTranExcl
  <2> QED BY <2>1, CTranLevelLE DEF CTranBelowProp
<1> SUFFICES ASSUME m \in CTran(p) PROVE FALSE  OBVIOUS
<1>3. m \in CMC /\ CMinLevel(m) <= CMinLevel(p)
  BY <1>2, CTranLevelLE DEF CTranBelowProp
<1>4. CMinLevel(p) \in Nat  BY <1>2, CMinLevelDom
<1>5. CMinLevel(m) \in Nat  BY CMinLevelDom
<1> QED BY <1>1, <1>3, <1>4, <1>5

LEMMA CTranTrans ==
  ASSUME NEW m \in CMC,
         NEW x \in CTran(m)
  PROVE CTran(x) \subseteq CTran(m)
<1> DEFINE lev(z) == CMinLevel(z)
<1> DEFINE Q(n) == \A mm \in CMC : lev(mm) = n =>
                     \A y \in CTran(mm) : CTran(y) \subseteq CTran(mm)
<1> SUFFICES \A n \in Nat : Q(n)  BY CMinLevelDom DEF Q
<1> HIDE DEF Q
<1>ind. \A n \in Nat : (\A kk \in 0..(n-1) : Q(kk)) => Q(n)
  <2> USE DEF Q
  <2> SUFFICES ASSUME NEW n \in Nat, \A kk \in 0..(n-1) : Q(kk),
                      NEW mm \in CMC, lev(mm) = n,
                      NEW y \in CTran(mm)
               PROVE  CTran(y) \subseteq CTran(mm)
    OBVIOUS
  <2>1. CTran(mm) = {mm} \cup UNION {CTran(p) : p \in CPriors(mm)}  BY CTranRec
  <2>2. CASE y = mm  BY <2>2
  <2>3. CASE y # mm
    <3>1. y \in UNION {CTran(p) : p \in CPriors(mm)}  BY <2>1, <2>3
    <3>2. PICK p \in CPriors(mm) : y \in CTran(p)  BY <3>1
    <3>3. p \in CMC  BY <3>2, CPriorsInMC
    <3>4. lev(p) < lev(mm)  BY <3>2, CPriorsDecreasesLevel
    <3>5. lev(p) \in Nat  BY <3>3, CMinLevelDom
    <3>6. lev(p) \in 0..(n-1)  BY <3>4, <3>5
    <3>7. CTran(y) \subseteq CTran(p)  BY <3>2, <3>3, <3>6
    <3>8. CTran(p) \in {CTran(pp) : pp \in CPriors(mm)}  BY <3>2
    <3>9. CTran(p) \subseteq CTran(mm)  BY <3>8, <2>1
    <3> QED BY <3>7, <3>9
  <2> QED BY <2>2, <2>3
<1> QED BY <1>ind, GeneralNatInduction, IsaM("blast")

CRefs(m) == {x \in CTranExcl(m) :
            (\A y \in CTranExcl(m): y = x \/ x \notin CTran(y))}

CIsProposal(m) == m.payload \in CProposal
CIsReply(m) == m.payload \in CReply

CB(m) == Max({x.payload.ballot : x \in {y \in CTran(m) : CIsProposal(y)}})

CSig(m) == m.sender
CSigS(S) == {CSig(x) : x \in S}

CV(m) == BalToVal(CB(m))

\* Mirrors MessageInterface's IsOneB.  The abstract interface exposes no "reply"
\* concept, so IsOneB is "not a proposal, with exactly two same-ballot messages
\* in its closure"; on CMessages, m \notin Proposals <=> ~CIsProposal(m), so we
\* use ~CIsProposal here (CProposals is not yet in scope -- it depends on
\* CMessages, which depends on this).  Keeping CIsOneB in lockstep with abstract
\* IsOneB is required for CHasDepth to match the abstract HasDepth.
CIsOneB(m) == ~CIsProposal(m) /\ Cardinality({x \in CTran(m) : CB(x) = CB(m)}) = 2

CCaughtS(S) == {a \in Acceptors:
  \E m1 \in S : \E m2 \in S:
    /\ CSig(m1) = a
    /\ CSig(m2) = a
    /\ m1 \notin CTran(m2)
    /\ m2 \notin CTran(m1)}
CCaught(m) == CCaughtS(CTran(m))
CCon(alpha, x) == ConFromCaught(alpha, CCaught(x))

\* Duplicated from MessageInterface.tla's CombinedFreshQdLrnsIdR, operating
\* on the raw record structure instead of the abstract .tran/.sig fields.
CCflR(x, r) ==
  LET qdx == [pr \in Learners \X Nat |->
       LET alpha == pr[1]
           d     == pr[2]
       IN  {y.id: y \in {mm \in r:
     /\ d > 0
     /\ CB(mm.id) = CB(x)
     /\ CSig(mm.id) \in Acceptors
     /\ d = 1 => (CIsOneB(mm.id) /\ mm.fresh[alpha])
     /\ d > 1 => CSigS(mm.qd[<<alpha, d-1>>]) \in Quorums(alpha)
     }}]
  IN
  [ id |-> x,
    qd |-> qdx,
    lrns  |-> {alpha \in Learners:
                 CSig(x) \in Acceptors /\ CSigS(qdx[<<alpha, 1>>]) \in Quorums(alpha)},
    fresh |-> [alpha \in Learners |->
      \A mm \in r:
        \/ CV(mm.id) = CV(x)
        \/ CCon(alpha, x) \cap mm.lrns = {}
        \/ \E p \in r:
          /\ CB(p.id) > CB(mm.id)
          /\ CCon(alpha, x) \cap p.lrns # {}
    ]
  ]

CCfl(x) == CRecursiveFunc(CCflR, CTranExcl, x)

CHasDepth(alpha, x, d) == CSig(x) \in Acceptors /\
  IF d=0 THEN (CIsOneB(x) /\ CCfl(x).fresh[alpha])
         ELSE CSigS(CCfl(x).qd[<<alpha, d>>]) \in Quorums(alpha)

\* Mirrors MessageInterface's IsTwoA: not a proposal, with depth 1 for some
\* learner (~CIsProposal stands in for m \notin Proposals, as in CIsOneB).
CIsTwoA(m) ==
  /\ ~CIsProposal(m)
  /\ \E alpha \in Learners: CHasDepth(alpha, m, 1)

CFilterOut(m) ==
  /\ CIsProposal(m) => CB(m) = m.payload.ballot
  /\ m.priors = CRefs(m)

CWellFormed(m) ==
  /\ \E a \in CTran(m) : CIsProposal(a)
  /\ CSig(m) \in Acceptors => CSig(m) \notin CCaught(m)
  /\ CIsProposal(m) \/ CIsOneB(m) \/ CIsTwoA(m)
  /\ CFilterOut(m)

CMessages == {m \in CMC : (\A x \in CTran(m): CWellFormed(x))}

LEMMA CMCShape == \A m \in CMC :
  m \in [sender : CSenders, payload : CPayload, priors : SUBSET CMC]
<1> SUFFICES ASSUME NEW m \in CMC
             PROVE m \in [sender : CSenders, payload : CPayload, priors : SUBSET CMC]
  OBVIOUS
<1>pri. m.priors \subseteq CMC  BY CPriorsInMC DEF CPriors
<1> DEFINE lev == CMinLevel(m)
<1>dom. lev \in Nat /\ m \in CMCAL[lev]
        /\ \A k \in Nat : m \in CMCAL[k] => lev <= k  BY CMinLevelDom
<1>2. CASE lev = 0
  <2>1. m \in CMCLBase  BY <1>dom, <1>2, CMCALUnfold
  <2>2. PICK r \in CSenders \X CPayload : m = [sender |-> r[1], payload |-> r[2], priors |-> {}]
    BY <2>1 DEF CMCLBase
  <2>3. m.sender = r[1] /\ m.payload = r[2] /\ r[1] \in CSenders /\ r[2] \in CPayload  BY <2>2
  <2> QED BY <2>2, <2>3, <1>pri
<1>3. CASE lev # 0
  <2>1. lev - 1 \in Nat  BY <1>dom, <1>3
  <2>2. m \notin CMCAL[lev-1]
    <3> SUFFICES ASSUME m \in CMCAL[lev-1] PROVE FALSE  OBVIOUS
    <3>1. lev <= lev - 1  BY <1>dom, <2>1
    <3> QED BY <3>1, <2>1, <1>dom
  <2>3. m \in CMCLExt(CMCAL[lev-1])  BY <1>dom, <1>3, CMCALUnfold
  <2>4. m \in CMCLNew(CMCAL[lev-1])  BY <2>3, <2>2 DEF CMCLExt
  <2>5. PICK r \in CSenders \X CPayload \X {x \in SUBSET CMCAL[lev-1] : IsFiniteSet(x)} :
          m = [sender |-> r[1], payload |-> r[2], priors |-> r[3]]  BY <2>4 DEF CMCLNew
  <2>6. m.sender = r[1] /\ m.payload = r[2] /\ r[1] \in CSenders /\ r[2] \in CPayload  BY <2>5
  <2> QED BY <2>5, <2>6, <1>pri
<1> QED BY <1>2, <1>3

LEMMA CSelfInTran == ASSUME NEW m \in CMC PROVE m \in CTran(m)
BY CTranRec

LEMMA CTranReflexiveSplit == ASSUME NEW m \in CMC PROVE CTran(m) = {m} \cup CTranExcl(m)
BY CSelfInTran DEF CTranExcl

LEMMA CMessagesSubMC == CMessages \subseteq CMC
BY DEF CMessages

LEMMA CMessageTranClosed ==
 ASSUME NEW m \in CMessages
 PROVE CTran(m) \subseteq CMessages
<1>0. m \in CMC /\ (\A x \in CTran(m) : CWellFormed(x))  BY DEF CMessages
<1> SUFFICES ASSUME NEW y \in CTran(m) PROVE y \in CMessages  OBVIOUS
<1>1. y \in CMC  BY <1>0, CTranLevelLE DEF CTranBelowProp
<1>2. CTran(y) \subseteq CTran(m)  BY <1>0, CTranTrans
<1>3. \A z \in CTran(y) : CWellFormed(z)  BY <1>0, <1>2
<1> QED BY <1>1, <1>3 DEF CMessages

\* ---- packaging into a MessageInterface record value ----
CProposals == {m \in CMessages : CIsProposal(m)}
CProposalBalField == [p \in CProposals |-> p.payload.ballot]
CSigField == [m \in CMessages |-> CSig(m)]
CTranField == [m \in CMessages |-> CTranExcl(m)]

CMI == [messages |-> CMessages, proposals |-> CProposals, senders |-> CSenders,
        sig |-> CSigField, proposalbal |-> CProposalBalField, tran |-> CTranField]

LEMMA CFields == ASSUME MessageInterface = CMI
  PROVE /\ Messages = CMessages
        /\ Proposals = CProposals
        /\ Senders = CSenders
  BY DEF Messages, Proposals, Senders, CMI

LEMMA CTranResolve == ASSUME MessageInterface = CMI, NEW m \in CMessages
  PROVE Tran(m) = CTran(m)
<1>1. Tran(m) = {m} \cup MessageInterface.tran[m]  BY DEF Tran
<1>2. MessageInterface.tran[m] = CTranExcl(m)  BY DEF CMI, CTranField
<1>3. Tran(m) = {m} \cup CTranExcl(m)  BY <1>1, <1>2
<1>4. m \in CMC  BY CMessagesSubMC
<1>5. CTran(m) = {m} \cup CTranExcl(m)  BY <1>4, CTranReflexiveSplit
<1> QED BY <1>3, <1>5

LEMMA CSigResolve == ASSUME MessageInterface = CMI, NEW m \in CMessages
  PROVE Sig(m) = CSig(m)
<1>1. Sig(m) = MessageInterface.sig[m]  BY DEF Sig
<1>2. MessageInterface.sig[m] = CSig(m)  BY DEF CMI, CSigField
<1> QED BY <1>1, <1>2

LEMMA CProposalBalResolve == ASSUME MessageInterface = CMI, NEW p \in CProposals
  PROVE ProposalBal(p) = p.payload.ballot
<1>1. ProposalBal(p) = MessageInterface.proposalbal[p]  BY DEF ProposalBal
<1>2. MessageInterface.proposalbal[p] = p.payload.ballot  BY DEF CMI, CProposalBalField
<1> QED BY <1>1, <1>2

\* ---- the structural MessageInterfaceAssumptions conjuncts ----
LEMMA CTypeOKMessageInterface == ASSUME MessageInterface = CMI PROVE TypeOKMessageInterface
<1>msg. Messages = CMessages  BY CFields
<1>prop. Proposals = CProposals  BY CFields
<1>send. Senders = CSenders  BY CFields
<1>1. MessageInterface.tran \in [Messages -> SUBSET Messages]
  <2>1. MessageInterface.tran = CTranField  BY DEF CMI
  <2>2. CTranField \in [CMessages -> SUBSET CMessages]
    <3> SUFFICES ASSUME NEW m \in CMessages PROVE CTranField[m] \in SUBSET CMessages
      BY DEF CTranField
    <3>1. CTranField[m] = CTranExcl(m)  BY DEF CTranField
    <3>2. CTranExcl(m) \subseteq CTran(m)  BY DEF CTranExcl
    <3>3. CTran(m) \subseteq CMessages  BY CMessageTranClosed
    <3> QED BY <3>1, <3>2, <3>3
  <2> QED BY <2>1, <2>2, <1>msg
<1>2. MessageInterface.sig \in [Messages -> Senders]
  <2>1. MessageInterface.sig = CSigField  BY DEF CMI
  <2>2. CSigField \in [CMessages -> CSenders]
    <3> SUFFICES ASSUME NEW m \in CMessages PROVE CSigField[m] \in CSenders
      BY DEF CSigField
    <3>1. CSigField[m] = CSig(m)  BY DEF CSigField
    <3>2. m \in CMC  BY CMessagesSubMC
    <3>3. m \in [sender : CSenders, payload : CPayload, priors : SUBSET CMC]  BY <3>2, CMCShape
    <3>4. CSig(m) = m.sender  BY DEF CSig
    <3> QED BY <3>1, <3>3, <3>4
  <2> QED BY <2>1, <2>2, <1>msg, <1>send
<1>3. Proposals \subseteq Messages  BY <1>msg, <1>prop DEF CProposals
<1>4. MessageInterface.proposalbal \in [Proposals -> Ballots]
  <2>1. MessageInterface.proposalbal = CProposalBalField  BY DEF CMI
  <2>2. CProposalBalField \in [CProposals -> Ballots]
    <3> SUFFICES ASSUME NEW p \in CProposals PROVE CProposalBalField[p] \in Ballots
      BY DEF CProposalBalField
    <3>1. CProposalBalField[p] = p.payload.ballot  BY DEF CProposalBalField
    <3>2. p.payload \in CProposal  BY DEF CProposals, CIsProposal
    <3>3. p.payload.ballot \in Ballots  BY <3>2 DEF CProposal
    <3> QED BY <3>1, <3>3
  <2> QED BY <2>1, <2>2, <1>prop
<1> QED BY <1>1, <1>2, <1>3, <1>4 DEF TypeOKMessageInterface

LEMMA CTranFinite == ASSUME MessageInterface = CMI PROVE TranFinite
<1> SUFFICES ASSUME NEW m \in Messages PROVE IsFiniteSet(Tran(m))  BY DEF TranFinite
<1>1. Messages = CMessages  BY CFields
<1>2. m \in CMessages  BY <1>1
<1>3. Tran(m) = CTran(m)  BY <1>2, CTranResolve
<1>4. m \in CMC  BY <1>2, CMessagesSubMC
<1>5. IsFiniteSet(CTran(m))  BY <1>4, CFiniteTran
<1> QED BY <1>3, <1>5

LEMMA CTranTransProof == ASSUME MessageInterface = CMI PROVE TranTrans
<1> SUFFICES ASSUME NEW m \in Messages, NEW x \in Tran(m) PROVE Tran(x) \subseteq Tran(m)
  BY DEF TranTrans
<1>1. Messages = CMessages  BY CFields
<1>2. m \in CMessages  BY <1>1
<1>3. Tran(m) = CTran(m)  BY <1>2, CTranResolve
<1>4. x \in CTran(m)  BY <1>3
<1>5. m \in CMC  BY <1>2, CMessagesSubMC
<1>6. x \in CMessages  BY <1>2, <1>4, CMessageTranClosed
<1>7. Tran(x) = CTran(x)  BY <1>6, CTranResolve
<1>8. CTran(x) \subseteq CTran(m)  BY <1>5, <1>4, CTranTrans
<1> QED BY <1>3, <1>7, <1>8

LEMMA CTranAcyclic == ASSUME MessageInterface = CMI PROVE TranAcyclic
<1> SUFFICES ASSUME NEW m \in Messages, NEW x \in TranExclusive(m) PROVE m \notin Tran(x)
  BY DEF TranAcyclic
<1>1. Messages = CMessages  BY CFields
<1>2. m \in CMessages  BY <1>1
<1>3. Tran(m) = CTran(m)  BY <1>2, CTranResolve
<1>4. TranExclusive(m) = CTranExcl(m)  BY <1>3 DEF TranExclusive, CTranExcl
<1>5. x \in CTranExcl(m)  BY <1>4
<1>6. m \in CMC  BY <1>2, CMessagesSubMC
<1>7. x \in CTran(m)  BY <1>5 DEF CTranExcl
<1>8. x \in CMessages  BY <1>2, <1>7, CMessageTranClosed
<1>9. Tran(x) = CTran(x)  BY <1>8, CTranResolve
<1>10. ~(m \in CTran(x))  BY <1>6, <1>5, CMCAcyclic
<1> QED BY <1>9, <1>10

LEMMA CAlwaysAProposal == ASSUME MessageInterface = CMI PROVE AlwaysAProposal
<1> SUFFICES ASSUME NEW m \in Messages PROVE GetProposals(m) # {}  BY DEF AlwaysAProposal
<1>1. Messages = CMessages  BY CFields
<1>2. m \in CMessages  BY <1>1
<1>3. Tran(m) = CTran(m)  BY <1>2, CTranResolve
<1>4. m \in CMC  BY <1>2, CMessagesSubMC
<1>5. \A x \in CTran(m) : CWellFormed(x)  BY <1>2 DEF CMessages
<1>6. m \in CTran(m)  BY <1>4, CSelfInTran
<1>7. CWellFormed(m)  BY <1>5, <1>6
<1>8. \E a \in CTran(m) : CIsProposal(a)  BY <1>7 DEF CWellFormed
<1> PICK a \in CTran(m) : CIsProposal(a)  BY <1>8
<1>9. a \in CMessages  BY <1>2, CMessageTranClosed
<1>10. a \in CProposals  BY <1>9 DEF CProposals
<1>11. Proposals = CProposals  BY CFields
<1>12. a \in Proposals  BY <1>10, <1>11
<1>13. a \in Tran(m)  BY <1>3
<1>14. a \in Proposals \cap Tran(m)  BY <1>12, <1>13
<1> QED BY <1>14 DEF GetProposals

LEMMA CAcceptorsSubsetSenders == ASSUME MessageInterface = CMI PROVE AcceptorsSubsetSenders
<1>1. Senders = CSenders  BY CFields
<1>2. Acceptors \subseteq CSenders  BY DEF CSenders
<1> QED BY <1>1, <1>2 DEF AcceptorsSubsetSenders

\* ---- machinery for the AlwaysANew* existence proofs ----

LEMMA CFiniteSubsetBounded ==
  ASSUME NEW S, IsFiniteSet(S), S \subseteq CMC
  PROVE \E L \in Nat : \A z \in S : z \in CMCAL[L]
<1> DEFINE Q(n) == \A T : (IsFiniteSet(T) /\ Cardinality(T) = n /\ T \subseteq CMC)
                          => (\E L \in Nat : \A z \in T : z \in CMCAL[L])
<1> SUFFICES \A n \in Nat : Q(n)
  <2>1. Cardinality(S) \in Nat  BY FS_CardinalityType
  <2> QED BY <2>1 DEF Q
<1> HIDE DEF Q
<1>ind. \A n \in Nat : (\A k \in 0..(n-1) : Q(k)) => Q(n)
  <2> USE DEF Q
  <2> SUFFICES ASSUME NEW n \in Nat, \A k \in 0..(n-1) : Q(k),
                      NEW T, IsFiniteSet(T), Cardinality(T) = n, T \subseteq CMC
               PROVE  \E L \in Nat : \A z \in T : z \in CMCAL[L]
    OBVIOUS
  <2>1. CASE T = {}
    <3> QED BY <2>1
  <2>2. CASE T # {}
    <3>x. PICK x \in T : TRUE  BY <2>2
    <3>pos. Cardinality(T) >= 1  BY FS_EmptySet, FS_CardinalityType
    <3>n1. n - 1 \in Nat  BY <3>pos
    <3>T2. IsFiniteSet(T \ {x}) /\ Cardinality(T \ {x}) = n - 1
      BY <3>x, FS_RemoveElement
    <3>T2sub. (T \ {x}) \subseteq CMC  BY <2>2
    <3>k. n - 1 \in 0..(n-1)  BY <3>n1
    <3>ih. \E L \in Nat : \A z \in (T \ {x}) : z \in CMCAL[L]
      BY <3>k, <3>T2, <3>T2sub
    <3> PICK L1 \in Nat : \A z \in (T \ {x}) : z \in CMCAL[L1]  BY <3>ih
    <3>picked. \A z \in (T \ {x}) : z \in CMCAL[L1]  OBVIOUS
    <3>xmc. x \in CMC  BY <3>x, <2>2
    <3>L2. CMinLevel(x) \in Nat /\ x \in CMCAL[CMinLevel(x)]  BY <3>xmc, CMinLevelDom
    <3> DEFINE Lmax == IF L1 >= CMinLevel(x) THEN L1 ELSE CMinLevel(x)
    <3>Lmaxnat. Lmax \in Nat  BY <3>L2
    <3>1. \A z \in (T \ {x}) : z \in CMCAL[Lmax]
      <4> SUFFICES ASSUME NEW z \in (T \ {x}) PROVE z \in CMCAL[Lmax]  OBVIOUS
      <4>1. z \in CMCAL[L1]  BY <3>picked
      <4> QED BY <4>1, <3>Lmaxnat, CMCALMonoGen
    <3>2. x \in CMCAL[Lmax]  BY <3>L2, <3>Lmaxnat, CMCALMonoGen
    <3>3. \A z \in T : z \in CMCAL[Lmax]
      <4> SUFFICES ASSUME NEW z \in T PROVE z \in CMCAL[Lmax]  OBVIOUS
      <4>1. CASE z = x  BY <4>1, <3>2
      <4>2. CASE z # x
        <5>1. z \in (T \ {x})  BY <4>2
        <5> QED BY <5>1, <3>1
      <4> QED BY <4>1, <4>2
    <3> QED BY <3>3, <3>Lmaxnat
  <2> QED BY <2>1, <2>2
<1> QED BY <1>ind, GeneralNatInduction, IsaM("blast")

LEMMA CMCFromShape ==
  ASSUME NEW rec \in [sender : CSenders, payload : CPayload, priors : SUBSET CMC],
         IsFiniteSet(rec.priors)
  PROVE  rec \in CMC
<1>1. rec.priors \subseteq CMC  OBVIOUS
<1>2. \E L \in Nat : \A z \in rec.priors : z \in CMCAL[L]  BY <1>1, CFiniteSubsetBounded
<1> PICK L \in Nat : \A z \in rec.priors : z \in CMCAL[L]  BY <1>2
<1>3. rec.priors \subseteq CMCAL[L]  OBVIOUS
<1>4. rec.priors \in {x2 \in SUBSET CMCAL[L] : IsFiniteSet(x2)}  BY <1>3
<1> DEFINE r == <<rec.sender, rec.payload, rec.priors>>
<1>5. r \in CSenders \X CPayload \X {x2 \in SUBSET CMCAL[L] : IsFiniteSet(x2)}  BY <1>4
<1>6. rec = [sender |-> r[1], payload |-> r[2], priors |-> r[3]]  OBVIOUS
<1>7. rec \in CMCLNew(CMCAL[L])  BY <1>5, <1>6 DEF CMCLNew
<1>8. CMCAL[L+1] = CMCLExt(CMCAL[L])
  <2>1. L + 1 # 0  OBVIOUS
  <2>2. (L+1) - 1 = L  OBVIOUS
  <2> QED BY <2>1, <2>2, CMCALUnfold
<1>9. rec \in CMCAL[L+1]  BY <1>7, <1>8 DEF CMCLExt
<1> QED BY <1>9 DEF CMC

\* If a freshly-built record's priors are exactly some finite S \subseteq CMC,
\* its CTranExcl is exactly UNION of S's Trans.
LEMMA CFreshTranExcl ==
  ASSUME NEW rec \in CMC, NEW S, rec.priors = S
  PROVE CTranExcl(rec) = UNION {CTran(q) : q \in S}
<1>1. CTran(rec) = {rec} \cup UNION {CTran(p) : p \in CPriors(rec)}  BY CTranRec
<1>2. CPriors(rec) = S  BY DEF CPriors
<1>3. CTran(rec) = {rec} \cup UNION {CTran(p) : p \in S}  BY <1>1, <1>2
<1>4. rec \notin UNION {CTran(p) : p \in S}
  <2> SUFFICES ASSUME rec \in UNION {CTran(p) : p \in S} PROVE FALSE  OBVIOUS
  <2>1. PICK p \in S : rec \in CTran(p)  OBVIOUS
  <2>Sub. CPriors(rec) \subseteq CMC  BY CPriorsInMC
  <2>2. p \in CMC  BY <2>1, <1>2, <2>Sub
  <2>3. CMinLevel(p) < CMinLevel(rec)  BY <1>2, CPriorsDecreasesLevel
  <2>4. rec \in CMC /\ CMinLevel(rec) <= CMinLevel(p)  BY <2>1, <2>2, CTranLevelLE DEF CTranBelowProp
  <2>5. CMinLevel(p) \in Nat /\ CMinLevel(rec) \in Nat  BY <2>2, CMinLevelDom
  <2> QED BY <2>3, <2>4, <2>5
<1> QED BY <1>3, <1>4 DEF CTranExcl

\* --- generalized MaxLevelElement / TranRefs machinery, for an ARBITRARY
\* finite Tran-closed set U (not tied to a specific message's own priors) ---

LEMMA CMaxLevelElement ==
  ASSUME NEW S, IsFiniteSet(S), S # {}, S \subseteq CMC
  PROVE \E x \in S : \A y \in S : CMinLevel(y) <= CMinLevel(x)
<1> DEFINE lev(z) == CMinLevel(z)
<1> DEFINE P(n) == \A T : (IsFiniteSet(T) /\ T # {} /\ Cardinality(T) = n /\ T \subseteq CMC)
                          => \E x \in T : \A y \in T : lev(y) <= lev(x)
<1>card. Cardinality(S) \in Nat  BY FS_CardinalityType
<1> SUFFICES \A n \in Nat : P(n)  BY <1>card
<1> HIDE DEF P
<1>ind. \A n \in Nat : (\A kk \in 0..(n-1) : P(kk)) => P(n)
  <2> USE DEF P
  <2> SUFFICES ASSUME NEW n \in Nat, \A kk \in 0..(n-1) : P(kk),
                      NEW T, IsFiniteSet(T), T # {}, Cardinality(T) = n, T \subseteq CMC
               PROVE  \E x \in T : \A y \in T : lev(y) <= lev(x)
    OBVIOUS
  <2>1. n # 0  BY FS_EmptySet
  <2>2. PICK x0 \in T : TRUE  OBVIOUS
  <2> DEFINE T0 == T \ {x0}
  <2>3. IsFiniteSet(T0) /\ T0 \subseteq CMC  BY FS_Subset
  <2>4. Cardinality(T0) = n - 1
    <3>1. T = T0 \cup {x0}  BY <2>2
    <3>2. x0 \notin T0  OBVIOUS
    <3>3. Cardinality(T) = Cardinality(T0) + 1  BY <2>3, <3>1, <3>2, FS_AddElement
    <3>4. Cardinality(T0) \in Nat  BY <2>3, FS_CardinalityType
    <3> QED BY <3>3, <3>4
  <2>5. CASE T0 = {}
    <3>1. T = {x0}  BY <2>2, <2>5
    <3>x0mc. x0 \in CMC  BY <2>2
    <3>x0lev. lev(x0) \in Nat  BY <3>x0mc, CMinLevelDom
    <3>2. \A y \in T : lev(y) <= lev(x0)
      <4> SUFFICES ASSUME NEW y \in T PROVE lev(y) <= lev(x0)  OBVIOUS
      <4>1. y = x0  BY <3>1
      <4>2. lev(x0) <= lev(x0)  BY <3>x0lev
      <4> QED BY <4>1, <4>2
    <3>3. x0 \in T /\ (\A y \in T : lev(y) <= lev(x0))  BY <2>2, <3>2
    <3> QED BY <3>3
  <2>6. CASE T0 # {}
    <3>k. n - 1 \in 0..(n-1)  BY <2>4, FS_CardinalityType, <2>3
    <3>ih. \E x \in T0 : \A y \in T0 : lev(y) <= lev(x)  BY <3>k, <2>3, <2>6, <2>4
    <3> PICK x1 \in T0 : \A y \in T0 : lev(y) <= lev(x1)  BY <3>ih
    <3>x1max. \A y \in T0 : lev(y) <= lev(x1)  OBVIOUS
    <3>x0mc. x0 \in CMC  BY <2>2
    <3>x1mc. x1 \in CMC  BY <2>3
    <3>l0. lev(x0) \in Nat  BY <3>x0mc, CMinLevelDom
    <3>l1. lev(x1) \in Nat  BY <3>x1mc, CMinLevelDom
    <3>1. CASE lev(x0) >= lev(x1)
      <4>a. \A y \in T : lev(y) <= lev(x0)
        <5> SUFFICES ASSUME NEW y \in T PROVE lev(y) <= lev(x0)  OBVIOUS
        <5>1. CASE y = x0  BY <5>1, <3>l0
        <5>2. CASE y # x0
          <6>1. y \in T0  BY <5>2, <2>2
          <6>2. lev(y) <= lev(x1)  BY <6>1, <3>x1max
          <6>3. lev(y) \in Nat  BY <6>1, <2>3, CMinLevelDom
          <6> QED BY <6>2, <6>3, <3>1, <3>l0, <3>l1, SMT
        <5> QED BY <5>1, <5>2
      <4>witness. x0 \in T /\ (\A y \in T : lev(y) <= lev(x0))  BY <2>2, <4>a
      <4> QED BY <4>witness
    <3>2. CASE lev(x0) < lev(x1)
      <4>a. \A y \in T : lev(y) <= lev(x1)
        <5> SUFFICES ASSUME NEW y \in T PROVE lev(y) <= lev(x1)  OBVIOUS
        <5>1. CASE y = x0  BY <5>1, <3>2, <3>l0, <3>l1
        <5>2. CASE y # x0
          <6>1. y \in T0  BY <5>2, <2>2
          <6> QED BY <6>1, <3>x1max
        <5> QED BY <5>1, <5>2
      <4>x1T. x1 \in T  BY <2>2
      <4>witness. x1 \in T /\ (\A y \in T : lev(y) <= lev(x1))  BY <4>x1T, <4>a
      <4> QED BY <4>witness
    <3> QED BY <3>1, <3>2, <3>l0, <3>l1
  <2> QED BY <2>5, <2>6
<1> QED BY <1>ind, GeneralNatInduction, IsaM("blast")

CMMax(U) == {x \in U : \A y \in U : x \notin CTranExcl(y)}

\* Generalization of HPaxos's TranRefs: for a finite, Tran-closed set U, the
\* "maximal antichain within U" (CMMax(U)) has the same Tran-image as U
\* itself.  Same "climb to a maximal dominator" argument as TranRefs, just
\* over an arbitrary closed U instead of TranExclusive(m) for an existing m.
LEMMA CGenTranRefs ==
  ASSUME NEW U, IsFiniteSet(U), U \subseteq CMC, \A x \in U : CTran(x) \subseteq U
  PROVE U = UNION {CTran(x) : x \in CMMax(U)}
<1>closed. \A x \in U : CTran(x) \subseteq U  OBVIOUS
<1>sup. UNION {CTran(x) : x \in CMMax(U)} \subseteq U
  <2> SUFFICES ASSUME NEW x \in CMMax(U), NEW z \in CTran(x) PROVE z \in U  OBVIOUS
  <2>1. x \in U  BY DEF CMMax
  <2>2. CTran(x) \subseteq U  BY <2>1, <1>closed
  <2> QED BY <2>2
<1>sub. U \subseteq UNION {CTran(x) : x \in CMMax(U)}
  <2> SUFFICES ASSUME NEW z \in U PROVE z \in UNION {CTran(x) : x \in CMMax(U)}  OBVIOUS
  <2>zmc. z \in CMC  OBVIOUS
  <2>zz. z \in CTran(z)  BY <2>zmc, CSelfInTran
  <2> DEFINE cand == {y \in U : z \in CTran(y)}
  <2>c1. cand \subseteq CMC  OBVIOUS
  <2>c2. cand # {}  BY <2>zz
  <2>c3. IsFiniteSet(cand)  BY FS_Subset
  <2>x. PICK x \in cand : \A y \in cand : CMinLevel(y) <= CMinLevel(x)  BY <2>c1, <2>c2, <2>c3, CMaxLevelElement
  <2>x1. x \in U /\ z \in CTran(x)  BY <2>x
  <2>x3. x \in CMC  BY <2>x1
  <2>x4. x \in CMMax(U)
    <3> SUFFICES ASSUME NEW y \in U, x \in CTranExcl(y) PROVE FALSE
      BY <2>x1 DEF CMMax
    <3>1. y \in CMC  OBVIOUS
    <3>2. x \in CTran(y)  BY DEF CTranExcl
    <3>3. CTran(x) \subseteq CTran(y)  BY <3>1, <3>2, CTranTrans
    <3>4. z \in CTran(y)  BY <2>x1, <3>3
    <3>5. y \in cand  BY <3>4
    <3>6. CMinLevel(x) < CMinLevel(y)  BY <3>1, CTranExclDecreasesLevel
    <3>7. CMinLevel(y) <= CMinLevel(x)  BY <3>5, <2>x
    <3>8. CMinLevel(x) \in Nat /\ CMinLevel(y) \in Nat  BY <2>x3, <3>1, CMinLevelDom
    <3> QED BY <3>6, <3>7, <3>8
  <2> QED BY <2>x1, <2>x4
<1> QED BY <1>sup, <1>sub

LEMMA CMaxSubsetMonotone ==
  ASSUME NEW S1, NEW S2, IsFiniteSet(S2), S1 \subseteq S2, S1 # {}, \A z \in S2 : z \in Nat
  PROVE Max(S1) <= Max(S2)
<1>1. IsFiniteSet(S1)  BY FS_Subset
<1>2. \A z \in S1 : z \in Nat  OBVIOUS
<1>3. \E r \in S1 : \A y \in S1 : y <= r  BY <1>1, FiniteSetHasMax
<1> PICK r1 \in S1 : \A y \in S1 : y <= r1  BY <1>3
<1>4. Max(S1) \in S1 /\ (\A y \in S1 : Max(S1) >= y)  BY <1>1, <1>2, MaxProps
<1>5. \E r \in S2 : \A y \in S2 : y <= r  BY FiniteSetHasMax
<1> PICK r2 \in S2 : \A y \in S2 : y <= r2  BY <1>5
<1>6. Max(S2) \in S2 /\ (\A y \in S2 : Max(S2) >= y)  BY FS_EmptySet, MaxProps
<1>7. Max(S1) \in S2  BY <1>4
<1> QED BY <1>6, <1>7

\* If y is in x's Tran-closure (with x already Message-good), y's ballot
\* never exceeds x's -- x's proposal-set contains everything y's does.
LEMMA CBMonotone ==
  ASSUME NEW x \in CMessages, NEW y \in CTran(x)
  PROVE CB(y) <= CB(x)
<1>1. y \in CMessages  BY CMessageTranClosed
<1>2. x \in CMC  BY CMessagesSubMC
<1>3. y \in CMC  BY <1>1, CMessagesSubMC
<1>4. CTran(y) \subseteq CTran(x)  BY <1>2, CTranTrans
<1> DEFINE Px == {w \in CTran(x) : CIsProposal(w)}
<1> DEFINE Py == {w \in CTran(y) : CIsProposal(w)}
<1>5. Py \subseteq Px  BY <1>4
<1>6. IsFiniteSet(CTran(x))  BY <1>2, CFiniteTran
<1>7. IsFiniteSet(Px)  BY <1>6, FS_Subset
<1>8. Px # {}
  <2>0. x \in CTran(x)  BY <1>2, CSelfInTran
  <2>wf. \A z \in CTran(x) : CWellFormed(z)  BY DEF CMessages
  <2>1. CWellFormed(x)  BY <2>0, <2>wf
  <2>2. \E a \in CTran(x) : CIsProposal(a)  BY <2>1 DEF CWellFormed
  <2> QED BY <2>2
<1>9. Py # {}
  <2>0. y \in CTran(y)  BY <1>3, CSelfInTran
  <2>wf. \A z \in CTran(y) : CWellFormed(z)  BY <1>1 DEF CMessages
  <2>1. CWellFormed(y)  BY <2>0, <2>wf
  <2>2. \E a \in CTran(y) : CIsProposal(a)  BY <2>1 DEF CWellFormed
  <2> QED BY <2>2
<1> DEFINE ImgX == {w.payload.ballot : w \in Px}
<1> DEFINE ImgY == {w.payload.ballot : w \in Py}
<1>10. ImgY \subseteq ImgX  BY <1>5
<1>11. \A z \in ImgX : z \in Nat
  <2> SUFFICES ASSUME NEW w \in Px PROVE w.payload.ballot \in Nat  OBVIOUS
  <2>1. w \in CTran(x) /\ CIsProposal(w)  OBVIOUS
  <2>2. w.payload \in CProposal  BY <2>1 DEF CIsProposal
  <2>3. PICK bb \in Ballots : w.payload = [type |-> "proposal", ballot |-> bb]  BY <2>2 DEF CProposal
  <2>4. w.payload.ballot = bb  BY <2>3
  <2>5. bb \in Nat  BY DEF Ballots
  <2> QED BY <2>4, <2>5
<1>12. IsFiniteSet(ImgX)  BY <1>7, FS_Image
<1>13. ImgY # {}  BY <1>9
<1>14. Max(ImgY) <= Max(ImgX)  BY <1>12, <1>10, <1>13, <1>11, CMaxSubsetMonotone
<1> QED BY <1>14 DEF CB

LEMMA CBTypeNat ==
  ASSUME NEW x \in CMessages
  PROVE CB(x) \in Nat
<1>0. x \in CTran(x)  BY CMessagesSubMC, CSelfInTran
<1>wf. \A zz \in CTran(x) : CWellFormed(zz)  BY DEF CMessages
<1>1. CWellFormed(x)  BY <1>0, <1>wf
<1>2. \E a \in CTran(x) : CIsProposal(a)  BY <1>1 DEF CWellFormed
<1> DEFINE Px == {w \in CTran(x) : CIsProposal(w)}
<1>3. Px # {}  BY <1>2
<1>4. IsFiniteSet(CTran(x))  BY CMessagesSubMC, CFiniteTran
<1>5. IsFiniteSet(Px)  BY <1>4, FS_Subset
<1> DEFINE ImgX == {w.payload.ballot : w \in Px}
<1>6. \A z \in ImgX : z \in Nat
  <2> SUFFICES ASSUME NEW w \in Px PROVE w.payload.ballot \in Nat  OBVIOUS
  <2>1. w.payload \in CProposal  BY DEF CIsProposal
  <2>2. PICK bb \in Ballots : w.payload = [type |-> "proposal", ballot |-> bb]  BY <2>1 DEF CProposal
  <2>3. w.payload.ballot = bb  BY <2>2
  <2>4. bb \in Nat  BY DEF Ballots
  <2> QED BY <2>3, <2>4
<1>7. IsFiniteSet(ImgX)  BY <1>5, FS_Image
<1>8. ImgX # {}  BY <1>3
<1>9. Max(ImgX) \in ImgX  BY <1>7, <1>8, <1>6, MaxProps
<1> QED BY <1>9, <1>6 DEF CB

\* The Tran-closure of a finite subset of CMessages is finite, stays inside
\* CMessages, and is itself Tran-closed -- everything CGenTranRefs needs.
LEMMA CUnionTranFiniteClosed ==
  ASSUME NEW m, IsFiniteSet(m), m \subseteq CMessages
  PROVE /\ IsFiniteSet(UNION {CTran(x) : x \in m})
        /\ UNION {CTran(x) : x \in m} \subseteq CMessages
        /\ \A z \in UNION {CTran(x) : x \in m} : CTran(z) \subseteq UNION {CTran(x) : x \in m}
<1> DEFINE U == UNION {CTran(x) : x \in m}
<1>mmc. m \subseteq CMC  BY CMessagesSubMC
<1>fin. IsFiniteSet(U)
  <2>1. \A x \in m : IsFiniteSet(CTran(x))  BY <1>mmc, CFiniteTran
  <2>2. IsFiniteSet({CTran(x) : x \in m})  BY FS_Image
  <2> QED BY <2>1, <2>2, FS_UNION
<1>sub. U \subseteq CMessages
  <2> SUFFICES ASSUME NEW z \in U PROVE z \in CMessages  OBVIOUS
  <2>1. PICK x \in m : z \in CTran(x)  OBVIOUS
  <2>2. CTran(x) \subseteq CMessages  BY CMessageTranClosed
  <2> QED BY <2>1, <2>2
<1>closed. \A z \in U : CTran(z) \subseteq U
  <2> SUFFICES ASSUME NEW z \in U PROVE CTran(z) \subseteq U  OBVIOUS
  <2>1. PICK x \in m : z \in CTran(x)  OBVIOUS
  <2>2. x \in CMC  BY <1>mmc
  <2>3. CTran(z) \subseteq CTran(x)  BY <2>2, <2>1, CTranTrans
  <2>4. CTran(x) \subseteq U  BY <2>1
  <2> QED BY <2>3, <2>4
<1> QED BY <1>fin, <1>sub, <1>closed

\* B(x) resolves to CB(x) for any already-Message x, given MessageInterface=CMI.
LEMMA CBResolve == ASSUME MessageInterface = CMI, NEW x \in CMessages
  PROVE B(x) = CB(x)
<1>1. B(x) = Max({ProposalBal(y) : y \in GetProposals(x)})  BY DEF B
<1>2. GetProposals(x) = Proposals \cap Tran(x)  BY DEF GetProposals
<1>3. Proposals = CProposals  BY CFields
<1>4. Tran(x) = CTran(x)  BY CTranResolve
<1>5. GetProposals(x) = CProposals \cap CTran(x)  BY <1>2, <1>3, <1>4
<1>6. CTran(x) \subseteq CMessages  BY CMessageTranClosed
<1>7. CProposals \cap CTran(x) = {y \in CTran(x) : CIsProposal(y)}
  <2> SUFFICES ASSUME NEW y \in CTran(x)
               PROVE y \in CProposals <=> CIsProposal(y)
    OBVIOUS
  <2>1. y \in CMessages  BY <1>6
  <2> QED BY <2>1 DEF CProposals
<1>8. GetProposals(x) = {y \in CTran(x) : CIsProposal(y)}  BY <1>5, <1>7
<1>9. \A y \in GetProposals(x) : ProposalBal(y) = y.payload.ballot
  <2> SUFFICES ASSUME NEW y \in GetProposals(x) PROVE ProposalBal(y) = y.payload.ballot
    OBVIOUS
  <2>1. y \in CProposals  BY <1>5
  <2> QED BY <2>1, CProposalBalResolve
<1>10. {ProposalBal(y) : y \in GetProposals(x)} = {y.payload.ballot : y \in {y \in CTran(x) : CIsProposal(y)}}
  BY <1>8, <1>9
<1> QED BY <1>1, <1>10 DEF CB

LEMMA CAlwaysANewProposal == ASSUME MessageInterface = CMI PROVE AlwaysANewProposal
<1> SUFFICES ASSUME NEW m \in SUBSET Messages, NEW b \in Ballots,
                    IsFiniteSet(m), \A x \in m : B(x) < b
             PROVE \E p \in Proposals :
                     /\ TranExclusive(p) = TranClosure(m)
                     /\ B(p) = b
                     /\ Sig(p) \notin Acceptors
  BY DEF AlwaysANewProposal
<1>msgeq. Messages = CMessages  BY CFields
<1>mmc. m \subseteq CMessages  BY <1>msgeq
<1>bhyp. \A x \in m : CB(x) < b
  <2> SUFFICES ASSUME NEW x \in m PROVE CB(x) < b  OBVIOUS
  <2>1. x \in CMessages  BY <1>mmc
  <2>2. B(x) = CB(x)  BY <2>1, CBResolve
  <2> QED BY <2>2

\* --- U, PP, prec construction ---
<1> DEFINE U == UNION {CTran(x) : x \in m}
<1>Uprops. IsFiniteSet(U) /\ U \subseteq CMessages /\ (\A z \in U : CTran(z) \subseteq U)
  BY <1>mmc, CUnionTranFiniteClosed
<1>Ufin. IsFiniteSet(U)  BY <1>Uprops
<1>Usub. U \subseteq CMessages  BY <1>Uprops
<1>Uclosed. \A z \in U : CTran(z) \subseteq U  BY <1>Uprops
<1>UsubCMC. U \subseteq CMC  BY <1>Usub, CMessagesSubMC

<1> DEFINE PP == CMMax(U)
<1>ppEq. U = UNION {CTran(x) : x \in PP}  BY <1>Ufin, <1>UsubCMC, <1>Uclosed, CGenTranRefs
<1>ppSub. PP \subseteq U  BY DEF CMMax
<1>ppSubCMC. PP \subseteq CMC  BY <1>ppSub, <1>UsubCMC
<1>ppFin. IsFiniteSet(PP)  BY <1>ppSub, <1>Ufin, FS_Subset

<1>bsend. CProposerSender \in CSenders  BY DEF CSenders
<1>bnat. b \in Nat  BY DEF Ballots
<1>bpay. [type |-> "proposal", ballot |-> b] \in CProposal  BY <1>bnat DEF CProposal
<1> DEFINE prec == [sender |-> CProposerSender, payload |-> [type |-> "proposal", ballot |-> b], priors |-> PP]
<1>precShape. prec \in [sender : CSenders, payload : CPayload, priors : SUBSET CMC]
  BY <1>bsend, <1>bpay, <1>ppSubCMC DEF CPayload
<1>precMC. prec \in CMC  BY <1>precShape, <1>ppFin, CMCFromShape
<1>precPriors. prec.priors = PP  OBVIOUS
<1>precTE0. CTranExcl(prec) = UNION {CTran(q) : q \in PP}  BY <1>precMC, <1>precPriors, CFreshTranExcl
<1>precTEeqU. CTranExcl(prec) = U  BY <1>precTE0, <1>ppEq

\* --- CWellFormed(prec) ---
<1>precIsProp. CIsProposal(prec)  BY DEF CIsProposal, CProposal
<1>precSelf. prec \in CTran(prec)  BY <1>precMC, CSelfInTran
<1>precHasProp. \E a \in CTran(prec) : CIsProposal(a)  BY <1>precSelf, <1>precIsProp
<1>precSig. CSig(prec) = CProposerSender  BY DEF CSig
<1>precNotAcc. CProposerSender \notin Acceptors  BY CProposerSenderNotAcceptor
<1>precNotCaughtVac. CSig(prec) \in Acceptors => CSig(prec) \notin CCaught(prec)
  BY <1>precSig, <1>precNotAcc
<1>precDisj. CIsProposal(prec) \/ CIsOneB(prec) \/ CIsTwoA(prec)  BY <1>precIsProp

<1>precTranSplit. CTran(prec) = {prec} \cup U
  <2>1. CTran(prec) = {prec} \cup CTranExcl(prec)  BY <1>precMC, CTranReflexiveSplit
  <2> QED BY <2>1, <1>precTEeqU

<1>Uballots. \A y \in U : CB(y) < b
  <2> SUFFICES ASSUME NEW y \in U PROVE CB(y) < b  OBVIOUS
  <2>1. PICK x \in m : y \in CTran(x)  OBVIOUS
  <2>2. x \in CMessages  BY <1>mmc
  <2>3. CB(y) <= CB(x)  BY <2>2, <2>1, CBMonotone
  <2>4. CB(x) < b  BY <1>bhyp, <2>1
  <2>5. y \in CMessages  BY <2>2, <2>1, CMessageTranClosed
  <2>6. CB(y) \in Nat  BY <2>5, CBTypeNat
  <2>7. CB(x) \in Nat  BY <2>2, CBTypeNat
  <2> QED BY <2>3, <2>4, <1>bnat, <2>6, <2>7

<1>precFilterBallot. CIsProposal(prec) => CB(prec) = prec.payload.ballot
  <2> DEFINE PropSet == {w \in CTran(prec) : CIsProposal(w)}
  <2> DEFINE ImgSet == {w.payload.ballot : w \in PropSet}
  <2>eq. PropSet = {prec} \cup {w \in U : CIsProposal(w)}  BY <1>precTranSplit, <1>precIsProp
  <2>imgEq. ImgSet = {b} \cup {w.payload.ballot : w \in {w \in U : CIsProposal(w)}}  BY <2>eq
  <2>bInImg. b \in ImgSet
    <3>1. prec \in PropSet  BY <1>precSelf, <1>precIsProp, <2>eq
    <3>2. prec.payload.ballot = b  OBVIOUS
    <3> QED BY <3>1, <3>2
  <2>ub. \A z \in ImgSet : z <= b
    <3> SUFFICES ASSUME NEW z \in ImgSet PROVE z <= b  OBVIOUS
    <3>1. CASE z = b  BY <3>1, <1>bnat
    <3>2. CASE z # b
      <4>1. PICK w \in {w \in U : CIsProposal(w)} : z = w.payload.ballot  BY <2>imgEq, <3>2
      <4>2. w \in U  BY <4>1
      <4>3. w \in CMessages  BY <4>2, <1>Usub
      <4>4. CB(w) < b  BY <4>2, <1>Uballots
      <4>5. w \in CTran(w)  BY <4>3, CMessagesSubMC, CSelfInTran
      <4>6. \A zz \in CTran(w) : CWellFormed(zz)  BY <4>3 DEF CMessages
      <4>7. CWellFormed(w)  BY <4>5, <4>6
      <4>8. CFilterOut(w)  BY <4>7 DEF CWellFormed
      <4>9. CIsProposal(w) => CB(w) = w.payload.ballot  BY <4>8 DEF CFilterOut
      <4>10. w.payload.ballot = CB(w)  BY <4>1, <4>9
      <4> QED BY <4>1, <4>10, <4>4
    <3> QED BY <3>1, <3>2
  <2>finImg. IsFiniteSet(ImgSet)
    <3>1. IsFiniteSet(CTran(prec))  BY <1>precMC, CFiniteTran
    <3>2. IsFiniteSet(PropSet)  BY <3>1, FS_Subset
    <3> QED BY <3>2, FS_Image
  <2>neImg. ImgSet # {}  BY <2>bInImg
  <2>natImg. \A z \in ImgSet : z \in Nat
    <3> SUFFICES ASSUME NEW w \in PropSet PROVE w.payload.ballot \in Nat  OBVIOUS
    <3>b. w.payload \in CProposal  BY DEF CIsProposal
    <3>c. PICK bb \in Ballots : w.payload = [type |-> "proposal", ballot |-> bb]  BY <3>b DEF CProposal
    <3>d. w.payload.ballot = bb  BY <3>c
    <3>e. bb \in Nat  BY DEF Ballots
    <3> QED BY <3>d, <3>e
  <2>maxprops. Max(ImgSet) \in ImgSet /\ (\A y \in ImgSet : Max(ImgSet) >= y)
    BY <2>finImg, <2>neImg, <2>natImg, MaxProps
  <2>maxNat. Max(ImgSet) \in Nat  BY <2>maxprops, <2>natImg
  <2>maxIsB. Max(ImgSet) = b
    <3>1. Max(ImgSet) <= b  BY <2>maxprops, <2>ub
    <3>2. Max(ImgSet) >= b  BY <2>maxprops, <2>bInImg
    <3> QED BY <3>1, <3>2, <2>maxNat, <1>bnat
  <2> QED BY <2>maxIsB DEF CB

<1>precFilterPriors. prec.priors = CRefs(prec)
  <2>1. CRefs(prec) = {x \in CTranExcl(prec) : (\A y \in CTranExcl(prec) : y = x \/ x \notin CTran(y))}
    BY DEF CRefs
  <2>2. CRefs(prec) = {x \in U : (\A y \in U : y = x \/ x \notin CTran(y))}  BY <2>1, <1>precTEeqU
  <2>3. CMMax(U) = {x \in U : \A y \in U : x \notin CTranExcl(y)}  BY DEF CMMax
  <2>4. \A x \in U : (\A y \in U : y = x \/ x \notin CTran(y)) <=> (\A y \in U : x \notin CTranExcl(y))
    <3> SUFFICES ASSUME NEW x \in U
                 PROVE (\A y \in U : y = x \/ x \notin CTran(y)) <=> (\A y \in U : x \notin CTranExcl(y))
      OBVIOUS
    <3>1. ASSUME NEW y \in U PROVE (y = x \/ x \notin CTran(y)) <=> (x \notin CTranExcl(y))
      BY DEF CTranExcl
    <3> QED BY <3>1
  <2>5. CRefs(prec) = CMMax(U)  BY <2>2, <2>3, <2>4
  <2> QED BY <2>5, <1>precPriors

<1>precFilter. CFilterOut(prec)
  BY <1>precFilterBallot, <1>precFilterPriors DEF CFilterOut

<1>precWF. CWellFormed(prec)
  BY <1>precHasProp, <1>precNotCaughtVac, <1>precDisj, <1>precFilter DEF CWellFormed

<1>allWF. \A z \in CTran(prec) : CWellFormed(z)
  <2> SUFFICES ASSUME NEW z \in CTran(prec) PROVE CWellFormed(z)  OBVIOUS
  <2>1. CASE z = prec  BY <2>1, <1>precWF
  <2>2. CASE z \in U
    <3>1. z \in CMessages  BY <1>Usub, <2>2
    <3>2. z \in CTran(z)  BY <3>1, CMessagesSubMC, CSelfInTran
    <3>3. \A zz \in CTran(z) : CWellFormed(zz)  BY <3>1 DEF CMessages
    <3> QED BY <3>2, <3>3
  <2> QED BY <1>precTranSplit, <2>1, <2>2

<1>precInMessages. prec \in CMessages  BY <1>precMC, <1>allWF DEF CMessages
<1>precInProposals. prec \in CProposals  BY <1>precInMessages, <1>precIsProp DEF CProposals
<1>propEq. Proposals = CProposals  BY CFields

\* --- resolve back to abstract Tran/TranExclusive/B/TranClosure/Proposals ---
<1>precAbsTran. Tran(prec) = CTran(prec)  BY <1>precInMessages, CTranResolve
<1>precAbsTE. TranExclusive(prec) = CTranExcl(prec)
  BY <1>precAbsTran DEF TranExclusive, CTranExcl
<1>precAbsTE2. TranExclusive(prec) = U  BY <1>precAbsTE, <1>precTEeqU
<1>tcEq. TranClosure(m) = U
  <2>1. TranClosure(m) = UNION {Tran(x) : x \in m}  BY DEF TranClosure
  <2>2. \A x \in m : Tran(x) = CTran(x)
    <3> SUFFICES ASSUME NEW x \in m PROVE Tran(x) = CTran(x)  OBVIOUS
    <3>1. x \in CMessages  BY <1>mmc
    <3> QED BY <3>1, CTranResolve
  <2> QED BY <2>1, <2>2
<1>precAbsTE3. TranExclusive(prec) = TranClosure(m)  BY <1>precAbsTE2, <1>tcEq
<1>precAbsB. B(prec) = CB(prec)  BY <1>precInMessages, CBResolve
<1>precB. B(prec) = b  BY <1>precAbsB, <1>precFilterBallot, <1>precIsProp
<1>precAbsSig. Sig(prec) = CSig(prec)  BY <1>precInMessages, CSigResolve
<1>precSigNotAcc. Sig(prec) \notin Acceptors  BY <1>precAbsSig, <1>precSig, <1>precNotAcc
<1> QED BY <1>precInProposals, <1>propEq, <1>precAbsTE3, <1>precB, <1>precSigNotAcc

\* ---- machinery for AlwaysANewOneB ----

\* Quorum non-emptiness, from ValidLearnerGraphAssumption + LearnersMightAgree.
LEMMA CQuorumNonEmpty ==
  ASSUME LearnersMightAgree, ValidLearnerGraphAssumption,
         NEW alpha \in Learners, NEW q \in Quorums(alpha)
  PROVE q # {}
<1>1. q \subseteq Acceptors  BY DEF Quorums
<1>2. Acceptors \in SafetySets({alpha,alpha})  BY DEF LearnersMightAgree, LearnerPairs
<1>3. (Acceptors \cap q \cap q) # {}  BY <1>2 DEF ValidLearnerGraphAssumption
<1>4. Acceptors \cap q \cap q = q  BY <1>1
<1> QED BY <1>3, <1>4

LEMMA CEmptyNotQuorum ==
  ASSUME LearnersMightAgree, ValidLearnerGraphAssumption, NEW alpha \in Learners
  PROVE {} \notin Quorums(alpha)
<1> SUFFICES ASSUME {} \in Quorums(alpha) PROVE FALSE  OBVIOUS
<1>1. {} # {}  BY CQuorumNonEmpty
<1> QED BY <1>1

\* Max of a proposal-ballot image is achieved by an actual proposal.
LEMMA CBAchievedByProposal ==
  ASSUME NEW x \in CMessages
  PROVE \E q \in CTran(x) : CIsProposal(q) /\ q.payload.ballot = CB(x)
<1>0. x \in CTran(x)  BY CMessagesSubMC, CSelfInTran
<1>wf. \A zz \in CTran(x) : CWellFormed(zz)  BY DEF CMessages
<1>1. CWellFormed(x)  BY <1>0, <1>wf
<1>2. \E aa \in CTran(x) : CIsProposal(aa)  BY <1>1 DEF CWellFormed
<1> DEFINE Px == {w \in CTran(x) : CIsProposal(w)}
<1>3. Px # {}  BY <1>2
<1>4. IsFiniteSet(CTran(x))  BY CMessagesSubMC, CFiniteTran
<1>5. IsFiniteSet(Px)  BY <1>4, FS_Subset
<1> DEFINE ImgX == {w.payload.ballot : w \in Px}
<1>6. \A z \in ImgX : z \in Nat
  <2> SUFFICES ASSUME NEW w \in Px PROVE w.payload.ballot \in Nat  OBVIOUS
  <2>1. w.payload \in CProposal  BY DEF CIsProposal
  <2>2. PICK bb \in Ballots : w.payload = [type |-> "proposal", ballot |-> bb]  BY <2>1 DEF CProposal
  <2>3. w.payload.ballot = bb  BY <2>2
  <2>4. bb \in Nat  BY DEF Ballots
  <2> QED BY <2>3, <2>4
<1>7. IsFiniteSet(ImgX)  BY <1>5, FS_Image
<1>8. ImgX # {}  BY <1>3
<1>9. Max(ImgX) \in ImgX  BY <1>7, <1>8, <1>6, MaxProps
<1>10. PICK q \in Px : q.payload.ballot = Max(ImgX)  BY <1>9
<1>11. Max(ImgX) = CB(x)  BY DEF CB
<1> QED BY <1>10, <1>11

\* A finite set of cardinality 1 is a singleton.
LEMMA CCardOneWitness ==
  ASSUME NEW S, IsFiniteSet(S), Cardinality(S) = 1
  PROVE \E s : S = {s}
<1>ne. S # {}  BY FS_EmptySet
<1> PICK s \in S : TRUE  BY <1>ne
<1>rm. IsFiniteSet(S \ {s}) /\ Cardinality(S \ {s}) = 0  BY FS_RemoveElement
<1>empty. S \ {s} = {}  BY <1>rm, FS_EmptySet
<1> QED BY <1>empty

\* CCfl unfolding (mirrors CTranRec, via the generic CRecursiveFuncRec).
LEMMA CCflRec == ASSUME NEW m \in CMC
  PROVE CCfl(m) = CCflR(m, {CCfl(y) : y \in CTranExcl(m)})
<1>1. \A x \in CMC : CTranExcl(x) \subseteq CMC
  <2> SUFFICES ASSUME NEW x \in CMC, NEW y \in CTranExcl(x) PROVE y \in CMC  OBVIOUS
  <2>1. y \in CTran(x)  BY DEF CTranExcl
  <2> QED BY <2>1, CTranLevelLE DEF CTranBelowProp
<1>2. \A x \in CMC : \A y \in CTranExcl(x) : CMinLevel(y) < CMinLevel(x)
  BY CTranExclDecreasesLevel
<1>3. CRecursiveFunc(CCflR, CTranExcl, m) =
        CCflR(m, {CRecursiveFunc(CCflR, CTranExcl, p) : p \in CTranExcl(m)})
  BY <1>1, <1>2, CRecursiveFuncRec
<1> QED BY <1>3 DEF CCfl

LEMMA CCflId == ASSUME NEW y \in CMC PROVE CCfl(y).id = y
BY CCflRec DEF CCflR

\* Resolve CaughtS on a set entirely inside CMessages.
LEMMA CCaughtSResolve ==
  ASSUME MessageInterface = CMI, NEW S, S \subseteq CMessages
  PROVE CaughtS(S) = CCaughtS(S)
<1>1. CaughtS(S) = {aa \in Acceptors :
        \E m1 \in S : \E m2 \in S :
          /\ Sig(m1) = aa /\ Sig(m2) = aa
          /\ m1 \notin Tran(m2) /\ m2 \notin Tran(m1)}
  BY DEF CaughtS
<1>2. \A m1 \in S : \A m2 \in S : Sig(m1) = CSig(m1) /\ Sig(m2) = CSig(m2)
  BY CSigResolve
<1>3. \A m1 \in S : \A m2 \in S : Tran(m1) = CTran(m1) /\ Tran(m2) = CTran(m2)
  BY CTranResolve
<1> QED BY <1>1, <1>2, <1>3 DEF CCaughtS

LEMMA CAlwaysANewOneB ==
  ASSUME MessageInterface = CMI, LearnersMightAgree, ValidLearnerGraphAssumption
  PROVE AlwaysANewOneB
<1> SUFFICES ASSUME NEW m \in SUBSET Messages, NEW b \in Ballots, NEW a \in Acceptors,
                    IsFiniteSet(m), \A x \in m : B(x) <= b,
                    Cardinality({x \in TranClosure(m) : B(x) = b}) = 1,
                    a \notin CaughtS(TranClosure(m))
             PROVE \E x \in Messages :
               (/\ Sig(x) = a
                /\ a \notin Caught(x)
                /\ IsOneB(x)
                /\ TranExclusive(x) = TranClosure(m))
  BY DEF AlwaysANewOneB
<1>msgeq. Messages = CMessages  BY CFields
<1>mmc. m \subseteq CMessages  BY <1>msgeq
<1>bnat. b \in Nat  BY DEF Ballots
<1>bhyp. \A x \in m : CB(x) <= b
  <2> SUFFICES ASSUME NEW x \in m PROVE CB(x) <= b  OBVIOUS
  <2>1. x \in CMessages  BY <1>mmc
  <2>2. B(x) = CB(x)  BY <2>1, CBResolve
  <2> QED BY <2>2

\* --- U construction ---
<1> DEFINE U == UNION {CTran(x) : x \in m}
<1>Uprops. IsFiniteSet(U) /\ U \subseteq CMessages /\ (\A z \in U : CTran(z) \subseteq U)
  BY <1>mmc, CUnionTranFiniteClosed
<1>Ufin. IsFiniteSet(U)  BY <1>Uprops
<1>Usub. U \subseteq CMessages  BY <1>Uprops
<1>Uclosed. \A z \in U : CTran(z) \subseteq U  BY <1>Uprops
<1>UsubCMC. U \subseteq CMC  BY <1>Usub, CMessagesSubMC

<1>tcEq. TranClosure(m) = U
  <2>1. TranClosure(m) = UNION {Tran(x) : x \in m}  BY DEF TranClosure
  <2>2. \A x \in m : Tran(x) = CTran(x)
    <3> SUFFICES ASSUME NEW x \in m PROVE Tran(x) = CTran(x)  OBVIOUS
    <3>1. x \in CMessages  BY <1>mmc
    <3> QED BY <3>1, CTranResolve
  <2> QED BY <2>1, <2>2

\* --- resolve the Cardinality=1 hypothesis to concrete terms, extract w0 ---
<1>cardsetEq. {x \in TranClosure(m) : B(x) = b} = {x \in U : CB(x) = b}
  <2>1. \A x \in U : B(x) = CB(x)  BY <1>Usub, CBResolve
  <2> QED BY <1>tcEq, <2>1
<1>cardhyp. Cardinality({x \in U : CB(x) = b}) = 1  BY <1>cardsetEq
<1>Ufinset. IsFiniteSet({x \in U : CB(x) = b})  BY <1>Ufin, FS_Subset
<1> PICK w0 : {x \in U : CB(x) = b} = {w0}  BY CCardOneWitness, <1>Ufinset, <1>cardhyp
<1>w0set. {x \in U : CB(x) = b} = {w0}  OBVIOUS
<1>w0mem. w0 \in {x \in U : CB(x) = b}  BY <1>w0set
<1>w0inU. w0 \in U /\ CB(w0) = b  BY <1>w0mem
<1>w0uniq. \A y \in U : CB(y) = b => y = w0
  <2> SUFFICES ASSUME NEW y \in U, CB(y) = b PROVE y = w0  OBVIOUS
  <2>1. y \in {x \in U : CB(x) = b}  OBVIOUS
  <2> QED BY <2>1, <1>w0set

<1>Uball. \A y \in U : CB(y) <= b
  <2> SUFFICES ASSUME NEW y \in U PROVE CB(y) <= b  OBVIOUS
  <2>1. PICK x \in m : y \in CTran(x)  OBVIOUS
  <2>2. x \in CMessages  BY <1>mmc
  <2>3. CB(y) <= CB(x)  BY <2>2, <2>1, CBMonotone
  <2>4. CB(x) <= b  BY <1>bhyp, <2>1
  <2>5. y \in CMessages  BY <2>2, <2>1, CMessageTranClosed
  <2>6. CB(y) \in Nat  BY <2>5, CBTypeNat
  <2>7. CB(x) \in Nat  BY <2>2, CBTypeNat
  <2> QED BY <2>3, <2>4, <1>bnat, <2>6, <2>7

\* --- w0 must be a proposal ---
<1>w0msg. w0 \in CMessages  BY <1>Usub, <1>w0inU
<1>achieve. \E q \in CTran(w0) : CIsProposal(q) /\ q.payload.ballot = CB(w0)
  BY <1>w0msg, CBAchievedByProposal
<1> PICK q0 \in CTran(w0) : CIsProposal(q0) /\ q0.payload.ballot = CB(w0)  BY <1>achieve
<1>w0mc. w0 \in CMC  BY <1>w0msg, CMessagesSubMC
<1>q0inU. q0 \in U  BY <1>w0inU, <1>Uclosed
<1>q0msg. q0 \in CMessages  BY <1>q0inU, <1>Usub
<1>q0wf. CWellFormed(q0)
  <2>0. q0 \in CTran(q0)  BY <1>q0msg, CMessagesSubMC, CSelfInTran
  <2>wf. \A zz \in CTran(q0) : CWellFormed(zz)  BY <1>q0msg DEF CMessages
  <2> QED BY <2>0, <2>wf
<1>q0filter. CFilterOut(q0)  BY <1>q0wf DEF CWellFormed
<1>q0cb. CB(q0) = q0.payload.ballot  BY <1>achieve, <1>q0filter DEF CFilterOut
<1>q0cbb. CB(q0) = b  BY <1>q0cb, <1>achieve, <1>w0inU
<1>q0eqw0. q0 = w0  BY <1>q0inU, <1>q0cbb, <1>w0uniq
<1>w0isprop. CIsProposal(w0)  BY <1>q0eqw0, <1>achieve
<1>w0notreply. ~CIsReply(w0)  BY <1>w0isprop DEF CIsProposal, CIsReply, CProposal, CReply
\* w0 is a proposal, and OneBs are non-proposals, so w0 is not a OneB.
<1>w0notoneb. ~CIsOneB(w0)  BY <1>w0isprop DEF CIsOneB
<1>w0payb. w0.payload.ballot = b  BY <1>q0eqw0, <1>achieve, <1>w0inU

\* --- build the fresh reply record xrec ---
<1> DEFINE PP == CMMax(U)
<1>ppEq. U = UNION {CTran(x) : x \in PP}  BY <1>Ufin, <1>UsubCMC, <1>Uclosed, CGenTranRefs
<1>ppSub. PP \subseteq U  BY DEF CMMax
<1>ppSubCMC. PP \subseteq CMC  BY <1>ppSub, <1>UsubCMC
<1>ppFin. IsFiniteSet(PP)  BY <1>ppSub, <1>Ufin, FS_Subset

<1>asend. a \in CSenders  BY DEF CSenders
<1>replypay. [type |-> "reply"] \in CReply  BY DEF CReply
<1> DEFINE xrec == [sender |-> a, payload |-> [type |-> "reply"], priors |-> PP]
<1>xrecShape. xrec \in [sender : CSenders, payload : CPayload, priors : SUBSET CMC]
  BY <1>asend, <1>replypay, <1>ppSubCMC DEF CPayload
<1>xrecMC. xrec \in CMC  BY <1>xrecShape, <1>ppFin, CMCFromShape
<1>xrecPriors. xrec.priors = PP  OBVIOUS
<1>xrecTE0. CTranExcl(xrec) = UNION {CTran(q) : q \in PP}
  BY <1>xrecMC, <1>xrecPriors, CFreshTranExcl
<1>xrecTEeqU. CTranExcl(xrec) = U  BY <1>xrecTE0, <1>ppEq
<1>xrecTranSplit. CTran(xrec) = {xrec} \cup U
  <2>1. CTran(xrec) = {xrec} \cup CTranExcl(xrec)  BY <1>xrecMC, CTranReflexiveSplit
  <2> QED BY <2>1, <1>xrecTEeqU
<1>xrecNotInU. xrec \notin U  BY <1>xrecTEeqU DEF CTranExcl

<1>xrecIsReply. CIsReply(xrec)  BY <1>replypay DEF CIsReply
<1>xrecNotProp. ~CIsProposal(xrec)
  BY <1>xrecIsReply DEF CIsProposal, CIsReply, CProposal, CReply

\* --- CB(xrec) = b ---
<1>xrecCB. CB(xrec) = b
  <2> DEFINE Px == {w \in CTran(xrec) : CIsProposal(w)}
  <2> DEFINE ImgSet == {w.payload.ballot : w \in Px}
  <2>PxEq. Px = {w \in U : CIsProposal(w)}  BY <1>xrecTranSplit, <1>xrecNotProp
  <2>bInImg. b \in ImgSet
    <3>1. w0 \in Px  BY <1>w0inU, <1>w0isprop, <2>PxEq
    <3> QED BY <3>1, <1>w0payb
  <2>ub. \A z \in ImgSet : z <= b
    <3> SUFFICES ASSUME NEW z \in ImgSet PROVE z <= b  OBVIOUS
    <3>1. PICK w \in Px : z = w.payload.ballot  OBVIOUS
    <3>2. w \in U /\ CIsProposal(w)  BY <3>1, <2>PxEq
    <3>3. w \in CMessages  BY <3>2, <1>Usub
    <3>4. w \in CTran(w)  BY <3>3, CMessagesSubMC, CSelfInTran
    <3>5. \A zz \in CTran(w) : CWellFormed(zz)  BY <3>3 DEF CMessages
    <3>6. CWellFormed(w)  BY <3>4, <3>5
    <3>7. CFilterOut(w)  BY <3>6 DEF CWellFormed
    <3>8. CIsProposal(w) => CB(w) = w.payload.ballot  BY <3>7 DEF CFilterOut
    <3>9. w.payload.ballot = CB(w)  BY <3>2, <3>8
    <3>10. CB(w) <= b  BY <3>2, <1>Uball
    <3> QED BY <3>1, <3>9, <3>10
  <2>finImg. IsFiniteSet(ImgSet)
    <3>1. IsFiniteSet(CTran(xrec))  BY <1>xrecMC, CFiniteTran
    <3>2. IsFiniteSet(Px)  BY <3>1, FS_Subset
    <3> QED BY <3>2, FS_Image
  <2>neImg. ImgSet # {}  BY <2>bInImg
  <2>natImg. \A z \in ImgSet : z \in Nat
    <3> SUFFICES ASSUME NEW w \in Px PROVE w.payload.ballot \in Nat  OBVIOUS
    <3>b. w.payload \in CProposal  BY DEF CIsProposal
    <3>c. PICK bb \in Ballots : w.payload = [type |-> "proposal", ballot |-> bb]  BY <3>b DEF CProposal
    <3>d. w.payload.ballot = bb  BY <3>c
    <3>e. bb \in Nat  BY DEF Ballots
    <3> QED BY <3>d, <3>e
  <2>maxprops. Max(ImgSet) \in ImgSet /\ (\A y \in ImgSet : Max(ImgSet) >= y)
    BY <2>finImg, <2>neImg, <2>natImg, MaxProps
  <2>maxNat. Max(ImgSet) \in Nat  BY <2>maxprops, <2>natImg
  <2>maxIsB. Max(ImgSet) = b
    <3>1. Max(ImgSet) <= b  BY <2>maxprops, <2>ub
    <3>2. Max(ImgSet) >= b  BY <2>maxprops, <2>bInImg
    <3> QED BY <3>1, <3>2, <2>maxNat, <1>bnat
  <2> QED BY <2>maxIsB DEF CB

\* --- xrec is OneB ---
<1>matchset. {y \in CTran(xrec) : CB(y) = b} = {xrec, w0}
  <2>1. {y \in U : CB(y) = b} = {w0}  BY <1>w0set
  <2> QED BY <1>xrecTranSplit, <1>xrecCB, <2>1
<1>xrecNEw0. xrec # w0  BY <1>xrecNotInU, <1>w0inU
<1>card2. Cardinality({xrec, w0}) = 2
  <2>1. Cardinality({xrec}) = 1  BY FS_Singleton
  <2>2. IsFiniteSet({xrec})  BY FS_Singleton
  <2>3. w0 \notin {xrec}  BY <1>xrecNEw0
  <2>4. {xrec, w0} = {xrec} \cup {w0}  OBVIOUS
  <2>5. Cardinality({xrec} \cup {w0}) = Cardinality({xrec}) + 1  BY <2>2, <2>3, FS_AddElement
  <2> QED BY <2>1, <2>4, <2>5
<1>xrecOneB. CIsOneB(xrec)  BY <1>xrecNotProp, <1>matchset, <1>card2, <1>xrecCB DEF CIsOneB

\* --- xrec.priors = CRefs(xrec) ---
<1>xrecFilterPriors. xrec.priors = CRefs(xrec)
  <2>1. CRefs(xrec) = {x \in CTranExcl(xrec) : (\A y \in CTranExcl(xrec) : y = x \/ x \notin CTran(y))}
    BY DEF CRefs
  <2>2. CRefs(xrec) = {x \in U : (\A y \in U : y = x \/ x \notin CTran(y))}  BY <2>1, <1>xrecTEeqU
  <2>3. CMMax(U) = {x \in U : \A y \in U : x \notin CTranExcl(y)}  BY DEF CMMax
  <2>4. \A x \in U : (\A y \in U : y = x \/ x \notin CTran(y)) <=> (\A y \in U : x \notin CTranExcl(y))
    <3> SUFFICES ASSUME NEW x \in U
                 PROVE (\A y \in U : y = x \/ x \notin CTran(y)) <=> (\A y \in U : x \notin CTranExcl(y))
      OBVIOUS
    <3>1. ASSUME NEW y \in U PROVE (y = x \/ x \notin CTran(y)) <=> (x \notin CTranExcl(y))
      BY DEF CTranExcl
    <3> QED BY <3>1
  <2>5. CRefs(xrec) = CMMax(U)  BY <2>2, <2>3, <2>4
  <2> QED BY <2>5, <1>xrecPriors

\* --- CFilterOut(xrec) ---
<1>xrecFilterProp. CIsProposal(xrec) => CB(xrec) = xrec.payload.ballot  BY <1>xrecNotProp
<1>xrecFilter. CFilterOut(xrec)
  BY <1>xrecFilterProp, <1>xrecFilterPriors DEF CFilterOut

\* --- has-a-proposal witness ---
<1>xrecHasProp. \E qq \in CTran(xrec) : CIsProposal(qq)
  <2>1. w0 \in CTran(xrec)  BY <1>w0inU, <1>xrecTranSplit
  <2> QED BY <2>1, <1>w0isprop

\* --- sig / not-caught ---
<1>xrecSig. CSig(xrec) = a  BY DEF CSig
<1>caughtSResolve. CaughtS(U) = CCaughtS(U)  BY <1>Usub, CCaughtSResolve
<1>abscaughtU. a \notin CaughtS(U)
  <2>1. a \notin CaughtS(TranClosure(m))  OBVIOUS
  <2> QED BY <2>1, <1>tcEq
<1>conccaughtU. a \notin CCaughtS(U)  BY <1>abscaughtU, <1>caughtSResolve
<1>notcaught. a \notin CCaughtS(CTran(xrec))
  <2> SUFFICES ASSUME NEW m1 \in CTran(xrec), NEW m2 \in CTran(xrec), CSig(m1) = a, CSig(m2) = a
               PROVE m1 \in CTran(m2) \/ m2 \in CTran(m1)
    BY DEF CCaughtS
  <2>1. CASE m1 \in U /\ m2 \in U
    <3> SUFFICES ASSUME ~(m1 \in CTran(m2) \/ m2 \in CTran(m1)) PROVE FALSE  OBVIOUS
    <3>1. m1 \notin CTran(m2) /\ m2 \notin CTran(m1)  OBVIOUS
    <3>2. a \in CCaughtS(U)  BY <2>1, <3>1 DEF CCaughtS
    <3> QED BY <3>2, <1>conccaughtU
  <2>2. CASE m1 = xrec
    <3>0. m2 \in U \/ m2 = xrec  BY <1>xrecTranSplit
    <3>1. CASE m2 \in U
      <4>1. m2 \in CTran(xrec)  BY <3>1, <1>xrecTranSplit
      <4> QED BY <2>2, <4>1
    <3>2. CASE m2 = xrec
      <4>1. xrec \in CTran(xrec)  BY <1>xrecMC, CSelfInTran
      <4> QED BY <2>2, <3>2, <4>1
    <3> QED BY <3>0, <3>1, <3>2
  <2>3. CASE m2 = xrec
    <3>0. m1 \in U \/ m1 = xrec  BY <1>xrecTranSplit
    <3>1. CASE m1 \in U
      <4>1. m1 \in CTran(xrec)  BY <3>1, <1>xrecTranSplit
      <4> QED BY <2>3, <4>1
    <3>2. CASE m1 = xrec
      <4>1. xrec \in CTran(xrec)  BY <1>xrecMC, CSelfInTran
      <4> QED BY <2>3, <3>2, <4>1
    <3> QED BY <3>0, <3>1, <3>2
  <2>0. (m1 \in U \/ m1 = xrec) /\ (m2 \in U \/ m2 = xrec)  BY <1>xrecTranSplit
  <2> QED BY <2>0, <2>1, <2>2, <2>3, <1>xrecTranSplit

\* --- CWellFormed(xrec) ---
<1>xrecNotCaughtVac. CSig(xrec) \in Acceptors => CSig(xrec) \notin CCaught(xrec)
  BY <1>xrecSig, <1>notcaught DEF CCaught
<1>xrecDisj. CIsProposal(xrec) \/ CIsOneB(xrec) \/ CIsTwoA(xrec)  BY <1>xrecOneB
<1>xrecWF. CWellFormed(xrec)
  BY <1>xrecHasProp, <1>xrecNotCaughtVac, <1>xrecDisj, <1>xrecFilter DEF CWellFormed

<1>allWF. \A z \in CTran(xrec) : CWellFormed(z)
  <2> SUFFICES ASSUME NEW z \in CTran(xrec) PROVE CWellFormed(z)  OBVIOUS
  <2>1. CASE z = xrec  BY <2>1, <1>xrecWF
  <2>2. CASE z \in U
    <3>1. z \in CMessages  BY <1>Usub, <2>2
    <3>2. z \in CTran(z)  BY <3>1, CMessagesSubMC, CSelfInTran
    <3>3. \A zz \in CTran(z) : CWellFormed(zz)  BY <3>1 DEF CMessages
    <3> QED BY <3>2, <3>3
  <2> QED BY <1>xrecTranSplit, <2>1, <2>2

<1>xrecInMessages. xrec \in CMessages  BY <1>xrecMC, <1>allWF DEF CMessages

\* --- resolve back to abstract ---
<1>xrecAbsSig. Sig(xrec) = a  BY <1>xrecInMessages, CSigResolve, <1>xrecSig
<1>xrecAbsTran. Tran(xrec) = CTran(xrec)  BY <1>xrecInMessages, CTranResolve
<1>xrecAbsTE. TranExclusive(xrec) = CTranExcl(xrec)
  BY <1>xrecAbsTran DEF TranExclusive, CTranExcl
<1>xrecAbsTE2. TranExclusive(xrec) = TranClosure(m)  BY <1>xrecAbsTE, <1>xrecTEeqU, <1>tcEq
<1>xrecAbsCaughtS. CaughtS(CTran(xrec)) = CCaughtS(CTran(xrec))
  <2>1. CTran(xrec) \subseteq CMessages  BY <1>xrecInMessages, CMessageTranClosed
  <2> QED BY <2>1, CCaughtSResolve
<1>xrecAbsCaught. Caught(xrec) = CCaughtS(CTran(xrec))
  BY <1>xrecAbsTran, <1>xrecAbsCaughtS DEF Caught
<1>xrecAbsNotCaught. a \notin Caught(xrec)  BY <1>xrecAbsCaught, <1>notcaught
<1>xrecAbsIsOneB. IsOneB(xrec)
  <2>1. IsOneB(xrec) = (~IsProposal(xrec) /\ Cardinality({x \in Tran(xrec) : B(x) = B(xrec)}) = 2)
    BY DEF IsOneB
  <2>np. ~IsProposal(xrec)
    <3>1. Proposals = CProposals  BY CFields
    <3>2. xrec \notin CProposals  BY <1>xrecNotProp, <1>xrecInMessages DEF CProposals
    <3> QED BY <3>1, <3>2 DEF IsProposal
  <2>2. \A x \in Tran(xrec) : x \in CMessages
    <3>1. Tran(xrec) = CTran(xrec)  BY <1>xrecAbsTran
    <3> QED BY <3>1, <1>xrecInMessages, CMessageTranClosed
  <2>3. \A x \in Tran(xrec) : B(x) = CB(x)  BY <2>2, CBResolve
  <2>4. B(xrec) = CB(xrec)  BY <1>xrecInMessages, CBResolve
  <2>5. {x \in Tran(xrec) : B(x) = B(xrec)} = {x \in CTran(xrec) : CB(x) = CB(xrec)}
    BY <1>xrecAbsTran, <2>3, <2>4
  <2> QED BY <2>1, <2>np, <2>5, <1>matchset, <1>card2, <1>xrecCB
<1> QED BY <1>msgeq, <1>xrecInMessages, <1>xrecAbsSig, <1>xrecAbsNotCaught, <1>xrecAbsIsOneB, <1>xrecAbsTE2

\* ===================================================================
\* Bridge: the abstract MessageInterface macros (SigS, IsProposal, IsOneB,
\* Caught, Con, V, HasDepth, IsTwoA) evaluated on the CMI instantiation agree
\* with their concrete C-prefixed counterparts on CMessages.  This lets the
\* AlwaysANew* existence proofs reason with the concrete recursion (CCfl) and
\* then transfer the result to the abstract goal.
\* ===================================================================

LEMMA CSigSResolve ==
  ASSUME MessageInterface = CMI, NEW S, S \subseteq CMessages
  PROVE SigS(S) = CSigS(S)
<1>1. SigS(S) = {Sig(xx) : xx \in S}  BY DEF SigS
<1>2. \A xx \in S : Sig(xx) = CSig(xx)  BY CSigResolve
<1> QED BY <1>1, <1>2 DEF CSigS

LEMMA CIsProposalResolve ==
  ASSUME MessageInterface = CMI, NEW x \in CMessages
  PROVE IsProposal(x) = CIsProposal(x)
<1>1. Proposals = CProposals  BY CFields
<1>2. IsProposal(x) <=> CIsProposal(x)  BY <1>1 DEF IsProposal, CProposals
<1>3. IsProposal(x) \in BOOLEAN  BY DEF IsProposal
<1>4. CIsProposal(x) \in BOOLEAN  BY DEF CIsProposal
<1> QED BY <1>2, <1>3, <1>4

LEMMA CIsOneBResolve ==
  ASSUME MessageInterface = CMI, NEW x \in CMessages
  PROVE IsOneB(x) = CIsOneB(x)
<1>prop. IsProposal(x) = CIsProposal(x)  BY CIsProposalResolve
<1>1. IsOneB(x) = (~IsProposal(x) /\ Cardinality({y \in Tran(x) : B(y) = B(x)}) = 2)  BY DEF IsOneB
<1>2. Tran(x) = CTran(x)  BY CTranResolve
<1>3. \A y \in CTran(x) : y \in CMessages  BY CMessageTranClosed
<1>4. \A y \in CTran(x) : B(y) = CB(y)  BY <1>3, CBResolve
<1>5. B(x) = CB(x)  BY CBResolve
<1>6. {y \in Tran(x) : B(y) = B(x)} = {y \in CTran(x) : CB(y) = CB(x)}  BY <1>2, <1>4, <1>5
<1> QED BY <1>1, <1>6, <1>prop DEF CIsOneB

LEMMA CCaughtResolve ==
  ASSUME MessageInterface = CMI, NEW x \in CMessages
  PROVE Caught(x) = CCaughtS(CTran(x))
<1>1. Caught(x) = CaughtS(Tran(x))  BY DEF Caught
<1>2. Tran(x) = CTran(x)  BY CTranResolve
<1>3. CTran(x) \subseteq CMessages  BY CMessageTranClosed
<1>4. CaughtS(CTran(x)) = CCaughtS(CTran(x))  BY <1>3, CCaughtSResolve
<1> QED BY <1>1, <1>2, <1>4

LEMMA CConResolve ==
  ASSUME MessageInterface = CMI, NEW alpha \in Learners, NEW x \in CMessages
  PROVE Con(alpha, x) = CCon(alpha, x)
<1>1. Con(alpha, x) = ConFromCaught(alpha, Caught(x))  BY DEF Con
<1>2. Caught(x) = CCaughtS(CTran(x))  BY CCaughtResolve
<1> QED BY <1>1, <1>2 DEF CCon, CCaught

LEMMA CVResolve ==
  ASSUME MessageInterface = CMI, NEW x \in CMessages
  PROVE V(x) = CV(x)
<1>1. V(x) = BalToVal(B(x))  BY DEF V
<1>2. B(x) = CB(x)  BY CBResolve
<1> QED BY <1>1, <1>2 DEF CV

\* a CCfl record's own qd images stay inside its subject's CTranExcl
LEMMA CQdSubset ==
  ASSUME NEW z \in CMC, NEW alpha \in Learners, NEW dd \in Nat
  PROVE CCfl(z).qd[<<alpha, dd>>] \subseteq CTranExcl(z)
<1> SUFFICES ASSUME NEW ee \in CCfl(z).qd[<<alpha, dd>>] PROVE ee \in CTranExcl(z)
  OBVIOUS
<1>1. CCfl(z) = CCflR(z, {CCfl(p) : p \in CTranExcl(z)})  BY CCflRec
<1>2. CCfl(z).qd = CCflR(z, {CCfl(p) : p \in CTranExcl(z)}).qd  BY <1>1
<1>3. CCfl(z).qd = [pr \in Learners \X Nat |->
        LET al == pr[1]  dl == pr[2]
        IN {yy.id : yy \in {mm \in {CCfl(p) : p \in CTranExcl(z)} :
              /\ dl > 0
              /\ CB(mm.id) = CB(z)
              /\ CSig(mm.id) \in Acceptors
              /\ dl = 1 => (CIsOneB(mm.id) /\ mm.fresh[al])
              /\ dl > 1 => CSigS(mm.qd[<<al, dl-1>>]) \in Quorums(al)}}]
  BY <1>2 DEF CCflR
<1>4. CCfl(z).qd[<<alpha, dd>>] =
        {yy.id : yy \in {mm \in {CCfl(p) : p \in CTranExcl(z)} :
              /\ dd > 0
              /\ CB(mm.id) = CB(z)
              /\ CSig(mm.id) \in Acceptors
              /\ dd = 1 => (CIsOneB(mm.id) /\ mm.fresh[alpha])
              /\ dd > 1 => CSigS(mm.qd[<<alpha, dd-1>>]) \in Quorums(alpha)}}
  BY <1>3
<1>5. \A p \in CTranExcl(z) : CCfl(p).id = p
  <2> SUFFICES ASSUME NEW p \in CTranExcl(z) PROVE CCfl(p).id = p  OBVIOUS
  <2>1. p \in CTran(z)  BY DEF CTranExcl
  <2>2. p \in CMC  BY <2>1, CTranLevelLE DEF CTranBelowProp
  <2> QED BY <2>2, CCflId
<1>6. PICK yy \in {mm \in {CCfl(p) : p \in CTranExcl(z)} : TRUE} : ee = yy.id
  BY <1>4
<1>7. PICK p \in CTranExcl(z) : yy = CCfl(p)  BY <1>6
<1>8. ee = CCfl(p).id  BY <1>6, <1>7
<1>9. ee = p  BY <1>8, <1>5, <1>7
<1> QED BY <1>9, <1>7

\* the big bridge: CombinedFreshQdLrnsId (abstract) = CCfl (concrete) on CMessages
LEMMA CCflResolve ==
  ASSUME MessageInterface = CMI
  PROVE \A x \in CMessages : CombinedFreshQdLrnsId(x) = CCfl(x)
<1> DEFINE Q(n) == \A x \in CMessages : CMinLevel(x) = n => CombinedFreshQdLrnsId(x) = CCfl(x)
<1> SUFFICES \A n \in Nat : Q(n)
  BY CMinLevelDom, CMessagesSubMC DEF Q
<1> HIDE DEF Q
<1>ind. \A n \in Nat : (\A k \in 0..(n-1) : Q(k)) => Q(n)
  <2> USE DEF Q
  <2> SUFFICES ASSUME NEW n \in Nat, \A k \in 0..(n-1) : Q(k),
                      NEW x \in CMessages, CMinLevel(x) = n
               PROVE CombinedFreshQdLrnsId(x) = CCfl(x)
    OBVIOUS
  <2>xmc. x \in CMC  BY CMessagesSubMC
  <2>xM. x \in Messages  BY CFields
  <2>tok. TypeOKMessageInterface  BY CTypeOKMessageInterface
  <2>ttr. TranTrans  BY CTranTransProof
  <2>tfin. TranFinite  BY CTranFinite
  <2>tac. TranAcyclic  BY CTranAcyclic
  <2>abs. CombinedFreshQdLrnsId(x) =
            CombinedFreshQdLrnsIdR(x, {CombinedFreshQdLrnsId(p) : p \in TranExclusive(x)})
    BY <2>xM, <2>tok, <2>ttr, <2>tfin, <2>tac, RecursiveMessageTranFuncRec
    DEF CombinedFreshQdLrnsId
  <2>conc. CCfl(x) = CCflR(x, {CCfl(p) : p \in CTranExcl(x)})  BY <2>xmc, CCflRec
  <2>teEq. TranExclusive(x) = CTranExcl(x)
    <3>1. Tran(x) = CTran(x)  BY CTranResolve
    <3> QED BY <3>1 DEF TranExclusive, CTranExcl
  <2>childMC. \A p \in CTranExcl(x) : p \in CMessages
    <3> SUFFICES ASSUME NEW p \in CTranExcl(x) PROVE p \in CMessages  OBVIOUS
    <3>1. p \in CTran(x)  BY DEF CTranExcl
    <3> QED BY <3>1, CMessageTranClosed
  <2>indHyp. \A p \in CTranExcl(x) : CombinedFreshQdLrnsId(p) = CCfl(p)
    <3> SUFFICES ASSUME NEW p \in CTranExcl(x) PROVE CombinedFreshQdLrnsId(p) = CCfl(p)  OBVIOUS
    <3>1. p \in CMessages  BY <2>childMC
    <3>2. p \in CMC  BY <3>1, CMessagesSubMC
    <3>3. CMinLevel(p) < CMinLevel(x)  BY <2>xmc, CTranExclDecreasesLevel
    <3>4. CMinLevel(p) \in Nat  BY <3>2, CMinLevelDom
    <3>5. CMinLevel(p) \in 0..(n-1)  BY <3>3, <3>4
    <3> QED BY <3>1, <3>5
  <2>setsEq. {CombinedFreshQdLrnsId(p) : p \in TranExclusive(x)} = {CCfl(p) : p \in CTranExcl(x)}
    BY <2>teEq, <2>indHyp
  <2> DEFINE r == {CCfl(p) : p \in CTranExcl(x)}
  <2>rchild. \A mm \in r : mm.id \in CTranExcl(x) /\ mm = CCfl(mm.id)
    <3> SUFFICES ASSUME NEW mm \in r PROVE mm.id \in CTranExcl(x) /\ mm = CCfl(mm.id)  OBVIOUS
    <3>a. PICK p \in CTranExcl(x) : mm = CCfl(p)  OBVIOUS
    <3>b. p \in CMC  BY <2>childMC, <3>a, CMessagesSubMC
    <3>c. CCfl(p).id = p  BY <3>b, CCflId
    <3> QED BY <3>a, <3>c
  <2> DEFINE qdxA == [pr \in Learners \X Nat |->
       LET al == pr[1]  dl == pr[2]
       IN {yy.id: yy \in {mm \in r:
             /\ dl > 0
             /\ B(mm.id) = B(x)
             /\ Sig(mm.id) \in Acceptors
             /\ dl = 1 => (IsOneB(mm.id) /\ mm.fresh[al])
             /\ dl > 1 => SigS(mm.qd[<<al, dl-1>>]) \in Quorums(al)}}]
  <2> DEFINE qdxC == [pr \in Learners \X Nat |->
       LET al == pr[1]  dl == pr[2]
       IN {yy.id: yy \in {mm \in r:
             /\ dl > 0
             /\ CB(mm.id) = CB(x)
             /\ CSig(mm.id) \in Acceptors
             /\ dl = 1 => (CIsOneB(mm.id) /\ mm.fresh[al])
             /\ dl > 1 => CSigS(mm.qd[<<al, dl-1>>]) \in Quorums(al)}}]
  <2>filterEq. \A al \in Learners, dl \in Nat :
      {mm \in r: /\ dl>0 /\ B(mm.id)=B(x) /\ Sig(mm.id) \in Acceptors /\ (dl=1=>(IsOneB(mm.id)/\mm.fresh[al]))
                 /\ (dl>1=>SigS(mm.qd[<<al,dl-1>>]) \in Quorums(al))}
    = {mm \in r: /\ dl>0 /\ CB(mm.id)=CB(x) /\ CSig(mm.id) \in Acceptors /\ (dl=1=>(CIsOneB(mm.id)/\mm.fresh[al]))
                 /\ (dl>1=>CSigS(mm.qd[<<al,dl-1>>]) \in Quorums(al))}
    <3> SUFFICES ASSUME NEW al \in Learners, NEW dl \in Nat, NEW mm \in r
                 PROVE (/\ dl>0 /\ B(mm.id)=B(x) /\ Sig(mm.id) \in Acceptors /\ (dl=1=>(IsOneB(mm.id)/\mm.fresh[al]))
                        /\ (dl>1=>SigS(mm.qd[<<al,dl-1>>]) \in Quorums(al)))
                    <=> (/\ dl>0 /\ CB(mm.id)=CB(x) /\ CSig(mm.id) \in Acceptors /\ (dl=1=>(CIsOneB(mm.id)/\mm.fresh[al]))
                        /\ (dl>1=>CSigS(mm.qd[<<al,dl-1>>]) \in Quorums(al)))
      OBVIOUS
    <3>pid. mm.id \in CTranExcl(x)  BY <2>rchild
    <3>pmc. mm.id \in CMessages  BY <3>pid, <2>childMC
    <3>bres. B(mm.id) = CB(mm.id)  BY <3>pmc, CBResolve
    <3>bxres. B(x) = CB(x)  BY CBResolve
    <3>sigacc. Sig(mm.id) = CSig(mm.id)  BY <3>pmc, CSigResolve
    <3>oneb. IsOneB(mm.id) = CIsOneB(mm.id)  BY <3>pmc, CIsOneBResolve
    <3>sigres. dl > 1 => SigS(mm.qd[<<al,dl-1>>]) = CSigS(mm.qd[<<al,dl-1>>])
      <4> SUFFICES ASSUME dl > 1 PROVE SigS(mm.qd[<<al,dl-1>>]) = CSigS(mm.qd[<<al,dl-1>>])
        OBVIOUS
      <4>nat. dl - 1 \in Nat  OBVIOUS
      <4>qdsub. mm.qd[<<al, dl-1>>] \subseteq CMessages
        <5>1. mm = CCfl(mm.id)  BY <2>rchild
        <5>2. mm.id \in CMC  BY <3>pmc, CMessagesSubMC
        <5>3. CCfl(mm.id).qd[<<al, dl-1>>] \subseteq CTranExcl(mm.id)  BY <5>2, <4>nat, CQdSubset
        <5>4. CTranExcl(mm.id) \subseteq CMessages
          <6> SUFFICES ASSUME NEW z \in CTranExcl(mm.id) PROVE z \in CMessages  OBVIOUS
          <6>1. z \in CTran(mm.id)  BY DEF CTranExcl
          <6> QED BY <6>1, <3>pmc, CMessageTranClosed
        <5> QED BY <5>1, <5>3, <5>4
      <4> QED BY <4>qdsub, CSigSResolve
    <3> QED BY <3>bres, <3>bxres, <3>sigacc, <3>oneb, <3>sigres
  <2>qdxptwise. \A al \in Learners, dl \in Nat : qdxA[<<al,dl>>] = qdxC[<<al,dl>>]
    <3> SUFFICES ASSUME NEW al \in Learners, NEW dl \in Nat PROVE qdxA[<<al,dl>>] = qdxC[<<al,dl>>]
      OBVIOUS
    <3>dom. <<al,dl>> \in Learners \X Nat  OBVIOUS
    <3>a. qdxA[<<al,dl>>] = {yy.id: yy \in {mm \in r:
             /\ dl > 0
             /\ B(mm.id) = B(x)
             /\ Sig(mm.id) \in Acceptors
             /\ dl = 1 => (IsOneB(mm.id) /\ mm.fresh[al])
             /\ dl > 1 => SigS(mm.qd[<<al, dl-1>>]) \in Quorums(al)}}
      BY <3>dom
    <3>c. qdxC[<<al,dl>>] = {yy.id: yy \in {mm \in r:
             /\ dl > 0
             /\ CB(mm.id) = CB(x)
             /\ CSig(mm.id) \in Acceptors
             /\ dl = 1 => (CIsOneB(mm.id) /\ mm.fresh[al])
             /\ dl > 1 => CSigS(mm.qd[<<al, dl-1>>]) \in Quorums(al)}}
      BY <3>dom
    <3>seteq. {mm \in r:
             /\ dl > 0
             /\ B(mm.id) = B(x)
             /\ Sig(mm.id) \in Acceptors
             /\ dl = 1 => (IsOneB(mm.id) /\ mm.fresh[al])
             /\ dl > 1 => SigS(mm.qd[<<al, dl-1>>]) \in Quorums(al)}
           = {mm \in r:
             /\ dl > 0
             /\ CB(mm.id) = CB(x)
             /\ CSig(mm.id) \in Acceptors
             /\ dl = 1 => (CIsOneB(mm.id) /\ mm.fresh[al])
             /\ dl > 1 => CSigS(mm.qd[<<al, dl-1>>]) \in Quorums(al)}
      \* keep r opaque: this is a pure instantiation of <2>filterEq, and
      \* unfolding r (= {CCfl(p) : ...}) blows the obligation past what the
      \* backends absorb
      <4> HIDE DEF r
      <4> QED BY <2>filterEq
    <3> QED BY <3>a, <3>c, <3>seteq
  <2>qdxEq. qdxA = qdxC
    <3> SUFFICES ASSUME NEW pr \in Learners \X Nat PROVE qdxA[pr] = qdxC[pr]
      OBVIOUS
    <3>1. pr = <<pr[1], pr[2]>> /\ pr[1] \in Learners /\ pr[2] \in Nat  OBVIOUS
    <3> QED BY <3>1, <2>qdxptwise
  <2>qdxAsub. \A al \in Learners, dl \in Nat : qdxA[<<al,dl>>] \subseteq CMessages
    <3> SUFFICES ASSUME NEW al \in Learners, NEW dl \in Nat, NEW ee \in qdxA[<<al,dl>>]
                 PROVE ee \in CMessages
      OBVIOUS
    <3>1. PICK mm \in r : ee = mm.id  OBVIOUS
    <3> QED BY <3>1, <2>rchild, <2>childMC
  <2>lrnsA. [al2 \in Learners |-> Sig(x) \in Acceptors /\ SigS(qdxA[<<al2,1>>]) \in Quorums(al2)]
          = [al2 \in Learners |-> CSig(x) \in Acceptors /\ CSigS(qdxC[<<al2,1>>]) \in Quorums(al2)]
    <3> SUFFICES ASSUME NEW al2 \in Learners
                 PROVE (Sig(x) \in Acceptors /\ SigS(qdxA[<<al2,1>>]) \in Quorums(al2))
                   <=> (CSig(x) \in Acceptors /\ CSigS(qdxC[<<al2,1>>]) \in Quorums(al2))
      OBVIOUS
    <3>sx. Sig(x) = CSig(x)  BY CSigResolve
    <3>1. qdxA[<<al2,1>>] \subseteq CMessages  BY <2>qdxAsub
    <3>2. SigS(qdxA[<<al2,1>>]) = CSigS(qdxA[<<al2,1>>])  BY <3>1, CSigSResolve
    <3> QED BY <3>sx, <3>2, <2>qdxEq
  <2>freshA. [al2 \in Learners |->
        \A mm \in r : \/ V(mm.id) = V(x)
                      \/ Con(al2, x) \cap mm.lrns = {}
                      \/ \E pp \in r : B(pp.id) > B(mm.id) /\ Con(al2, x) \cap pp.lrns # {}]
      = [al2 \in Learners |->
        \A mm \in r : \/ CV(mm.id) = CV(x)
                      \/ CCon(al2, x) \cap mm.lrns = {}
                      \/ \E pp \in r : CB(pp.id) > CB(mm.id) /\ CCon(al2, x) \cap pp.lrns # {}]
    <3> SUFFICES ASSUME NEW al2 \in Learners
                 PROVE (\A mm \in r : \/ V(mm.id) = V(x)
                                       \/ Con(al2, x) \cap mm.lrns = {}
                                       \/ \E pp \in r : B(pp.id) > B(mm.id) /\ Con(al2, x) \cap pp.lrns # {})
                    <=> (\A mm \in r : \/ CV(mm.id) = CV(x)
                                       \/ CCon(al2, x) \cap mm.lrns = {}
                                       \/ \E pp \in r : CB(pp.id) > CB(mm.id) /\ CCon(al2, x) \cap pp.lrns # {})
      OBVIOUS
    <3>vx. V(x) = CV(x)  BY CVResolve
    <3>conx. Con(al2, x) = CCon(al2, x)  BY CConResolve
    <3>each. \A mm \in r :
        (V(mm.id) = V(x) <=> CV(mm.id) = CV(x))
      <4> SUFFICES ASSUME NEW mm \in r PROVE V(mm.id) = V(x) <=> CV(mm.id) = CV(x)
        OBVIOUS
      <4>a. mm.id \in CMessages  BY <2>rchild, <2>childMC
      <4>b. V(mm.id) = CV(mm.id)  BY <4>a, CVResolve
      <4> QED BY <4>b, <3>vx
    <3>each2. \A mm \in r, pp \in r :
        (B(pp.id) > B(mm.id) <=> CB(pp.id) > CB(mm.id))
      <4> SUFFICES ASSUME NEW mm \in r, NEW pp \in r
                   PROVE B(pp.id) > B(mm.id) <=> CB(pp.id) > CB(mm.id)
        OBVIOUS
      <4>a. mm.id \in CMessages /\ pp.id \in CMessages  BY <2>rchild, <2>childMC
      <4>b. B(mm.id) = CB(mm.id) /\ B(pp.id) = CB(pp.id)  BY <4>a, CBResolve
      <4> QED BY <4>b
    <3> QED BY <3>each, <3>each2, <3>conx
  <2>Fapply. CombinedFreshQdLrnsIdR(x, r) = CCflR(x, r)
    BY <2>qdxEq, <2>lrnsA, <2>freshA DEF CombinedFreshQdLrnsIdR, CCflR
  <2> QED BY <2>abs, <2>conc, <2>setsEq, <2>Fapply
<1> QED BY <1>ind, GeneralNatInduction, IsaM("blast")

\* HasDepth (abstract) = CHasDepth (concrete), on CMessages
LEMMA CHasDepthResolve ==
  ASSUME MessageInterface = CMI, NEW x \in CMessages, NEW alpha \in Learners, NEW dd \in Nat
  PROVE HasDepth(alpha, x, dd) = CHasDepth(alpha, x, dd)
<1>1. CombinedFreshQdLrnsId(x) = CCfl(x)  BY CCflResolve
<1>sx. Sig(x) = CSig(x)  BY CSigResolve
<1>2. CASE dd = 0
  <2>1. HasDepth(alpha, x, dd) = (Sig(x) \in Acceptors /\ IsOneB(x) /\ CombinedFreshQdLrnsId(x).fresh[alpha])
    BY <1>2 DEF HasDepth
  <2>2. CHasDepth(alpha, x, dd) = (CSig(x) \in Acceptors /\ CIsOneB(x) /\ CCfl(x).fresh[alpha])
    BY <1>2 DEF CHasDepth
  <2>3. IsOneB(x) = CIsOneB(x)  BY CIsOneBResolve
  <2> QED BY <2>1, <2>2, <2>3, <1>1, <1>sx
<1>3. CASE dd # 0
  <2>1. HasDepth(alpha, x, dd) = (Sig(x) \in Acceptors /\ SigS(CombinedFreshQdLrnsId(x).qd[<<alpha, dd>>]) \in Quorums(alpha))
    BY <1>3 DEF HasDepth
  <2>2. CHasDepth(alpha, x, dd) = (CSig(x) \in Acceptors /\ CSigS(CCfl(x).qd[<<alpha, dd>>]) \in Quorums(alpha))
    BY <1>3 DEF CHasDepth
  <2>3. x \in CMC  BY CMessagesSubMC
  <2>4. CCfl(x).qd[<<alpha, dd>>] \subseteq CTranExcl(x)  BY <2>3, CQdSubset
  <2>5. CTranExcl(x) \subseteq CMessages
    <3> SUFFICES ASSUME NEW z \in CTranExcl(x) PROVE z \in CMessages  OBVIOUS
    <3>1. z \in CTran(x)  BY DEF CTranExcl
    <3> QED BY <3>1, CMessageTranClosed
  <2>6. CCfl(x).qd[<<alpha, dd>>] \subseteq CMessages  BY <2>4, <2>5
  <2>7. SigS(CCfl(x).qd[<<alpha, dd>>]) = CSigS(CCfl(x).qd[<<alpha, dd>>])  BY <2>6, CSigSResolve
  <2> QED BY <2>1, <2>2, <2>7, <1>1, <1>sx
<1> QED BY <1>2, <1>3

\* IsTwoA (abstract) = CIsTwoA (concrete), on CMessages
LEMMA CIsTwoAResolve ==
  ASSUME MessageInterface = CMI, NEW x \in CMessages
  PROVE IsTwoA(x) = CIsTwoA(x)
<1>prop. IsProposal(x) = CIsProposal(x)  BY CIsProposalResolve
<1>1. IsTwoA(x) = (~IsProposal(x) /\ \E alpha \in Learners : HasDepth(alpha, x, 1))  BY DEF IsTwoA
<1>2. \A alpha \in Learners : HasDepth(alpha, x, 1) = CHasDepth(alpha, x, 1)
  <2> SUFFICES ASSUME NEW alpha \in Learners PROVE HasDepth(alpha, x, 1) = CHasDepth(alpha, x, 1)
    OBVIOUS
  <2>1. 1 \in Nat  OBVIOUS
  <2> QED BY <2>1, CHasDepthResolve
<1> QED BY <1>1, <1>2, <1>prop DEF CIsTwoA

\* ===================================================================
\* AlwaysANewTwoA: a fresh depth-d TwoA signed by acceptor a, over the
\* transitive closure of m.  Its qd (acceptor-filtered, matching HasDepth's
\* own filter) equals the hypothesized quorum set exactly, giving depth d
\* directly; depth 1 (needed for IsTwoA) follows by downward closure.
\* ===================================================================

\* Concrete analogue of QdDef: computes a message's qd field at depth dd >= 1
\* as the set of its strict ancestors of matching ballot with depth dd-1.
LEMMA CQdCompute ==
  ASSUME NEW z \in CMC, NEW alpha \in Learners, NEW dd \in Nat, dd >= 1
  PROVE CCfl(z).qd[<<alpha, dd>>]
        = {p \in CTranExcl(z) : CB(p) = CB(z) /\ CHasDepth(alpha, p, dd-1)}
<1> DEFINE RR == {CCfl(p) : p \in CTranExcl(z)}
<1> DEFINE cond(mm) == /\ dd > 0
                       /\ CB(mm.id) = CB(z)
                       /\ CSig(mm.id) \in Acceptors
                       /\ dd = 1 => (CIsOneB(mm.id) /\ mm.fresh[alpha])
                       /\ dd > 1 => CSigS(mm.qd[<<alpha, dd-1>>]) \in Quorums(alpha)
<1>rec. CCfl(z) = CCflR(z, RR)  BY CCflRec
<1>dom. <<alpha, dd>> \in Learners \X Nat  OBVIOUS
<1>raw. CCfl(z).qd[<<alpha, dd>>] = {yy.id : yy \in {mm \in RR : cond(mm)}}
  BY <1>rec, <1>dom DEF CCflR
<1>id. \A p \in CTranExcl(z) : CCfl(p).id = p
  <2> SUFFICES ASSUME NEW p \in CTranExcl(z) PROVE CCfl(p).id = p  OBVIOUS
  <2>1. p \in CTran(z)  BY DEF CTranExcl
  <2>2. p \in CMC  BY <2>1, CTranLevelLE DEF CTranBelowProp
  <2> QED BY <2>2, CCflId
<1>cc. \A p \in CTranExcl(z) : cond(CCfl(p)) <=> (CB(p) = CB(z) /\ CHasDepth(alpha, p, dd-1))
  <2> SUFFICES ASSUME NEW p \in CTranExcl(z)
               PROVE cond(CCfl(p)) <=> (CB(p) = CB(z) /\ CHasDepth(alpha, p, dd-1))
    OBVIOUS
  <2>pid. CCfl(p).id = p  BY <1>id
  <2>hd. CHasDepth(alpha, p, dd-1) =
           (CSig(p) \in Acceptors /\
            IF dd-1 = 0 THEN (CIsOneB(p) /\ CCfl(p).fresh[alpha])
                        ELSE CSigS(CCfl(p).qd[<<alpha, dd-1>>]) \in Quorums(alpha))
    BY DEF CHasDepth
  <2>1. CASE dd = 1
    <3>a. cond(CCfl(p)) <=> (CB(p) = CB(z) /\ CSig(p) \in Acceptors /\ CIsOneB(p) /\ CCfl(p).fresh[alpha])
      BY <2>pid, <2>1
    <3>b. CHasDepth(alpha, p, dd-1) = (CSig(p) \in Acceptors /\ CIsOneB(p) /\ CCfl(p).fresh[alpha])
      BY <2>hd, <2>1
    <3> QED BY <3>a, <3>b
  <2>2. CASE dd > 1
    <3>a. cond(CCfl(p)) <=> (CB(p) = CB(z) /\ CSig(p) \in Acceptors
                             /\ CSigS(CCfl(p).qd[<<alpha, dd-1>>]) \in Quorums(alpha))
      BY <2>pid, <2>2
    <3>b. CHasDepth(alpha, p, dd-1) = (CSig(p) \in Acceptors
                             /\ CSigS(CCfl(p).qd[<<alpha, dd-1>>]) \in Quorums(alpha))
      <4>1. dd - 1 # 0  BY <2>2
      <4> QED BY <2>hd, <4>1
    <3> QED BY <3>a, <3>b
  <2> QED BY <2>1, <2>2
<1>sub. CCfl(z).qd[<<alpha, dd>>] \subseteq {p \in CTranExcl(z) : CB(p) = CB(z) /\ CHasDepth(alpha, p, dd-1)}
  <2> SUFFICES ASSUME NEW ee \in CCfl(z).qd[<<alpha, dd>>]
               PROVE ee \in {p \in CTranExcl(z) : CB(p) = CB(z) /\ CHasDepth(alpha, p, dd-1)}
    OBVIOUS
  <2>1. PICK yy \in {mm \in RR : cond(mm)} : ee = yy.id  BY <1>raw
  <2>2. yy \in RR /\ cond(yy)  BY <2>1
  <2>3. PICK p \in CTranExcl(z) : yy = CCfl(p)  BY <2>2
  <2>4. ee = p  BY <2>1, <2>3, <1>id
  <2>5. cond(CCfl(p))  BY <2>2, <2>3
  <2>6. CB(p) = CB(z) /\ CHasDepth(alpha, p, dd-1)  BY <2>5, <1>cc
  <2> QED BY <2>3, <2>4, <2>6
<1>sup. {p \in CTranExcl(z) : CB(p) = CB(z) /\ CHasDepth(alpha, p, dd-1)} \subseteq CCfl(z).qd[<<alpha, dd>>]
  <2> SUFFICES ASSUME NEW p \in CTranExcl(z), CB(p) = CB(z), CHasDepth(alpha, p, dd-1)
               PROVE p \in CCfl(z).qd[<<alpha, dd>>]
    OBVIOUS
  <2>1. CCfl(p) \in RR  OBVIOUS
  <2>2. cond(CCfl(p))  BY <1>cc
  <2>3. CCfl(p) \in {mm \in RR : cond(mm)}  BY <2>1, <2>2
  <2>4. CCfl(p).id = p  BY <1>id
  <2> QED BY <2>3, <2>4, <1>raw
<1> QED BY <1>sub, <1>sup

\* Quorums are upward-closed within finite subsets of Acceptors.
LEMMA CQuorumUpward ==
  ASSUME NEW l \in Learners, NEW s, NEW t,
         s \in Quorums(l), s \subseteq t, t \subseteq Acceptors, IsFiniteSet(t)
  PROVE t \in Quorums(l)
<1>1. \E mm \in GetSpecifiedQuorums(l) : mm \subseteq s  BY DEF Quorums
<1>2. \E mm \in GetSpecifiedQuorums(l) : mm \subseteq t  BY <1>1
<1> QED BY <1>2 DEF Quorums

\* Downward closure: given the depth-j quorum, every lower depth i <= j also
\* has a quorum of ballot-bb signatures in the Tran-closed set U.
LEMMA CDepthDownward ==
  ASSUME LearnersMightAgree, ValidLearnerGraphAssumption,
         NEW U, IsFiniteSet(U), U \subseteq CMessages,
         \A z \in U : CTran(z) \subseteq U,
         NEW alpha \in Learners, NEW bb, NEW j \in Nat,
         CSigS({p \in U : CB(p) = bb /\ CHasDepth(alpha, p, j)}) \in Quorums(alpha)
  PROVE \A i \in 0..j : CSigS({p \in U : CB(p) = bb /\ CHasDepth(alpha, p, i)}) \in Quorums(alpha)
<1> DEFINE W(n) == {p \in U : CB(p) = bb /\ CHasDepth(alpha, p, n)}
<1> DEFINE Q(n) == CSigS(W(n)) \in Quorums(alpha)
                     => \A i \in 0..n : CSigS(W(i)) \in Quorums(alpha)
<1> SUFFICES \A n \in Nat : Q(n)
  <2>1. j \in Nat  OBVIOUS
  <2> QED BY <2>1 DEF Q
<1> HIDE DEF Q
<1>ind. \A n \in Nat : (\A kk \in 0..(n-1) : Q(kk)) => Q(n)
  <2> USE DEF Q
  <2> SUFFICES ASSUME NEW n \in Nat, \A kk \in 0..(n-1) : Q(kk),
                      CSigS(W(n)) \in Quorums(alpha)
               PROVE \A i \in 0..n : CSigS(W(i)) \in Quorums(alpha)
    OBVIOUS
  <2>1. CASE n = 0
    <3> SUFFICES ASSUME NEW i \in 0..n PROVE CSigS(W(i)) \in Quorums(alpha)  OBVIOUS
    <3>1. i = 0  BY <2>1
    <3> QED BY <3>1, <2>1
  <2>2. CASE n >= 1
    <3>nn. n \in Nat /\ n >= 1  BY <2>2
    \* inline downward step: from the depth-n quorum, get the depth-(n-1) quorum
    <3>step. CSigS(W(n-1)) \in Quorums(alpha)
      <4>ne. W(n) # {}
        <5>1. CSigS(W(n)) # {}  BY CQuorumNonEmpty
        <5> QED BY <5>1 DEF CSigS
      <4>p. PICK p \in W(n) : TRUE  BY <4>ne
      <4>pU. p \in U /\ CB(p) = bb /\ CHasDepth(alpha, p, n)  BY <4>p
      <4>pmc. p \in CMC  BY <4>pU, CMessagesSubMC
      <4>hd. CHasDepth(alpha, p, n) =
               (CSig(p) \in Acceptors /\ CSigS(CCfl(p).qd[<<alpha, n>>]) \in Quorums(alpha))
        <5>1. n # 0  BY <3>nn
        <5> QED BY <5>1 DEF CHasDepth
      <4>quo. CSigS(CCfl(p).qd[<<alpha, n>>]) \in Quorums(alpha)  BY <4>hd, <4>pU
      <4>qd. CCfl(p).qd[<<alpha, n>>] = {q \in CTranExcl(p) : CB(q) = CB(p) /\ CHasDepth(alpha, q, n-1)}
        BY <4>pmc, <3>nn, CQdCompute
      <4>sub. CCfl(p).qd[<<alpha, n>>] \subseteq W(n-1)
        <5> SUFFICES ASSUME NEW q \in CCfl(p).qd[<<alpha, n>>] PROVE q \in W(n-1)  OBVIOUS
        <5>1. q \in CTranExcl(p) /\ CB(q) = CB(p) /\ CHasDepth(alpha, q, n-1)  BY <4>qd
        <5>2. q \in CTran(p)  BY <5>1 DEF CTranExcl
        <5>3. CTran(p) \subseteq U  BY <4>pU
        <5>4. q \in U  BY <5>2, <5>3
        <5>5. CB(q) = bb  BY <5>1, <4>pU
        <5> QED BY <5>4, <5>5, <5>1
      <4>sigsub. CSigS(CCfl(p).qd[<<alpha, n>>]) \subseteq CSigS(W(n-1))  BY <4>sub DEF CSigS
      <4>fin. IsFiniteSet(W(n-1))  BY FS_Subset
      <4>finsig. IsFiniteSet(CSigS(W(n-1)))  BY <4>fin, FS_Image DEF CSigS
      <4>acc. CSigS(W(n-1)) \subseteq Acceptors
        <5> SUFFICES ASSUME NEW aa \in CSigS(W(n-1)) PROVE aa \in Acceptors  OBVIOUS
        <5>1. PICK q \in W(n-1) : aa = CSig(q)  BY DEF CSigS
        <5>2. CHasDepth(alpha, q, n-1)  BY <5>1
        <5>3. CSig(q) \in Acceptors  BY <5>2 DEF CHasDepth
        <5> QED BY <5>1, <5>3
      <4> QED BY <4>quo, <4>sigsub, <4>acc, <4>finsig, CQuorumUpward
    <3>n1. n-1 \in 0..(n-1)  BY <2>2
    <3>Qn1. Q(n-1)  BY <3>n1
    <3>below. \A i \in 0..(n-1) : CSigS(W(i)) \in Quorums(alpha)  BY <3>Qn1, <3>step
    <3> SUFFICES ASSUME NEW i \in 0..n PROVE CSigS(W(i)) \in Quorums(alpha)  OBVIOUS
    <3>a. CASE i = n  BY <3>a
    <3>b. CASE i \in 0..(n-1)  BY <3>b, <3>below
    <3> QED BY <2>2, <3>a, <3>b
  <2> QED BY <2>1, <2>2
<1> QED BY <1>ind, GeneralNatInduction, IsaM("blast")

LEMMA CAlwaysANewTwoA ==
  ASSUME MessageInterface = CMI, LearnersMightAgree, ValidLearnerGraphAssumption
  PROVE AlwaysANewTwoA
<1> SUFFICES ASSUME NEW m \in SUBSET Messages, NEW b \in Ballots, NEW a \in Acceptors,
                    NEW alpha \in Learners, NEW d \in (1..(MaxDepth(alpha))),
                    IsFiniteSet(m), \A x \in m : B(x) <= b,
                    a \notin CaughtS(TranClosure(m)),
                    SigS({x \in TranClosure(m) :
                            B(x) = b /\ HasDepth(alpha, x, d-1)}) \in Quorums(alpha)
             PROVE \E x \in Messages :
               (/\ x \in TranClosure(m) \/ TranClosure(m) = TranExclusive(x)
                /\ B(x) = b
                /\ Sig(x) = a
                /\ HasDepth(alpha, x, d)
                /\ a \notin Caught(x)
                /\ IsTwoA(x))
  BY DEF AlwaysANewTwoA
<1>dnat. d \in Nat /\ d >= 1  OBVIOUS
<1>d1nat. d - 1 \in Nat  BY <1>dnat
<1>msgeq. Messages = CMessages  BY CFields
<1>mmc. m \subseteq CMessages  BY <1>msgeq
<1>bnat. b \in Nat  BY DEF Ballots
<1>bhyp. \A x \in m : CB(x) <= b
  <2> SUFFICES ASSUME NEW x \in m PROVE CB(x) <= b  OBVIOUS
  <2>1. x \in CMessages  BY <1>mmc
  <2>2. B(x) = CB(x)  BY <2>1, CBResolve
  <2> QED BY <2>2

\* --- U construction ---
<1> DEFINE U == UNION {CTran(x) : x \in m}
<1>Uprops. IsFiniteSet(U) /\ U \subseteq CMessages /\ (\A z \in U : CTran(z) \subseteq U)
  BY <1>mmc, CUnionTranFiniteClosed
<1>Ufin. IsFiniteSet(U)  BY <1>Uprops
<1>Usub. U \subseteq CMessages  BY <1>Uprops
<1>Uclosed. \A z \in U : CTran(z) \subseteq U  BY <1>Uprops
<1>UsubCMC. U \subseteq CMC  BY <1>Usub, CMessagesSubMC
<1>tcEq. TranClosure(m) = U
  <2>1. TranClosure(m) = UNION {Tran(x) : x \in m}  BY DEF TranClosure
  <2>2. \A x \in m : Tran(x) = CTran(x)
    <3> SUFFICES ASSUME NEW x \in m PROVE Tran(x) = CTran(x)  OBVIOUS
    <3>1. x \in CMessages  BY <1>mmc
    <3> QED BY <3>1, CTranResolve
  <2> QED BY <2>1, <2>2

\* --- resolve the acceptor-filtered quorum hypothesis to concrete form ---
<1> DEFINE AF == {p \in U : CB(p) = b /\ CHasDepth(alpha, p, d-1)}
<1>AFeq. {x \in TranClosure(m) : B(x) = b /\ HasDepth(alpha, x, d-1)} = AF
  <2> SUFFICES ASSUME NEW x \in U
               PROVE (B(x) = b /\ HasDepth(alpha, x, d-1))
                 <=> (CB(x) = b /\ CHasDepth(alpha, x, d-1))
    BY <1>tcEq
  <2>xmsg. x \in CMessages  BY <1>Usub
  <2>bx. B(x) = CB(x)  BY <2>xmsg, CBResolve
  <2>hx. HasDepth(alpha, x, d-1) = CHasDepth(alpha, x, d-1)  BY <2>xmsg, <1>d1nat, CHasDepthResolve
  <2> QED BY <2>bx, <2>hx
<1>sigsResolve. SigS(AF) = CSigS(AF)
  <2>1. AF \subseteq CMessages  BY <1>Usub
  <2> QED BY <2>1, CSigSResolve
<1>AFquo. CSigS(AF) \in Quorums(alpha)
  <2>1. SigS({x \in TranClosure(m) : B(x) = b /\ HasDepth(alpha, x, d-1)}) \in Quorums(alpha)
    OBVIOUS
  <2>2. SigS(AF) \in Quorums(alpha)  BY <2>1, <1>AFeq
  <2> QED BY <2>2, <1>sigsResolve

\* --- downward closure: all depths 0..d-1 have a ballot-b quorum in U ---
<1>downward. \A i \in 0..(d-1) : CSigS({p \in U : CB(p) = b /\ CHasDepth(alpha, p, i)}) \in Quorums(alpha)
  BY <1>Ufin, <1>Usub, <1>Uclosed, <1>d1nat, <1>AFquo, CDepthDownward

\* --- a ballot-b proposal exists in U (via a depth-(d-1) witness) ---
<1>AFne. AF # {}
  <2>1. CSigS(AF) # {}  BY <1>AFquo, CQuorumNonEmpty
  <2> QED BY <2>1 DEF CSigS
<1>w1. PICK w1 \in AF : TRUE  BY <1>AFne
<1>w1U. w1 \in U /\ CB(w1) = b  BY <1>w1
<1>w1msg. w1 \in CMessages  BY <1>w1U, <1>Usub
<1>achieve. \E q \in CTran(w1) : CIsProposal(q) /\ q.payload.ballot = CB(w1)
  BY <1>w1msg, CBAchievedByProposal
<1> PICK q0 \in CTran(w1) : CIsProposal(q0) /\ q0.payload.ballot = CB(w1)  BY <1>achieve
<1>q0inU. q0 \in U  BY <1>w1U, <1>Uclosed
<1>q0prop. CIsProposal(q0) /\ q0.payload.ballot = b  BY <1>achieve, <1>w1U

<1>Uball. \A y \in U : CB(y) <= b
  <2> SUFFICES ASSUME NEW y \in U PROVE CB(y) <= b  OBVIOUS
  <2>1. PICK x \in m : y \in CTran(x)  OBVIOUS
  <2>2. x \in CMessages  BY <1>mmc
  <2>3. CB(y) <= CB(x)  BY <2>2, <2>1, CBMonotone
  <2>4. CB(x) <= b  BY <1>bhyp, <2>1
  <2>5. y \in CMessages  BY <2>2, <2>1, CMessageTranClosed
  <2>6. CB(y) \in Nat  BY <2>5, CBTypeNat
  <2>7. CB(x) \in Nat  BY <2>2, CBTypeNat
  <2> QED BY <2>3, <2>4, <1>bnat, <2>6, <2>7

\* --- build the fresh reply record xrec, signed by a ---
<1> DEFINE PP == CMMax(U)
<1>ppEq. U = UNION {CTran(x) : x \in PP}  BY <1>Ufin, <1>UsubCMC, <1>Uclosed, CGenTranRefs
<1>ppSub. PP \subseteq U  BY DEF CMMax
<1>ppSubCMC. PP \subseteq CMC  BY <1>ppSub, <1>UsubCMC
<1>ppFin. IsFiniteSet(PP)  BY <1>ppSub, <1>Ufin, FS_Subset
<1>asend. a \in CSenders  BY DEF CSenders
<1>replypay. [type |-> "reply"] \in CReply  BY DEF CReply
<1> DEFINE xrec == [sender |-> a, payload |-> [type |-> "reply"], priors |-> PP]
<1>xrecShape. xrec \in [sender : CSenders, payload : CPayload, priors : SUBSET CMC]
  BY <1>asend, <1>replypay, <1>ppSubCMC DEF CPayload
<1>xrecMC. xrec \in CMC  BY <1>xrecShape, <1>ppFin, CMCFromShape
<1>xrecPriors. xrec.priors = PP  OBVIOUS
<1>xrecTE0. CTranExcl(xrec) = UNION {CTran(q) : q \in PP}  BY <1>xrecMC, <1>xrecPriors, CFreshTranExcl
<1>xrecTEeqU. CTranExcl(xrec) = U  BY <1>xrecTE0, <1>ppEq
<1>xrecTranSplit. CTran(xrec) = {xrec} \cup U
  <2>1. CTran(xrec) = {xrec} \cup CTranExcl(xrec)  BY <1>xrecMC, CTranReflexiveSplit
  <2> QED BY <2>1, <1>xrecTEeqU
<1>xrecNotInU. xrec \notin U  BY <1>xrecTEeqU DEF CTranExcl
<1>xrecIsReply. CIsReply(xrec)  BY <1>replypay DEF CIsReply
<1>xrecNotProp. ~CIsProposal(xrec)  BY <1>xrecIsReply DEF CIsProposal, CIsReply, CProposal, CReply
<1>xrecSig. CSig(xrec) = a  BY DEF CSig

\* --- CB(xrec) = b (max proposal ballot in U is b) ---
<1>xrecCB. CB(xrec) = b
  <2> DEFINE Px == {w \in CTran(xrec) : CIsProposal(w)}
  <2> DEFINE ImgSet == {w.payload.ballot : w \in Px}
  <2>PxEq. Px = {w \in U : CIsProposal(w)}  BY <1>xrecTranSplit, <1>xrecNotProp
  <2>bInImg. b \in ImgSet
    <3>1. q0 \in Px  BY <1>q0inU, <1>q0prop, <2>PxEq
    <3> QED BY <3>1, <1>q0prop
  <2>ub. \A z \in ImgSet : z <= b
    <3> SUFFICES ASSUME NEW z \in ImgSet PROVE z <= b  OBVIOUS
    <3>1. PICK w \in Px : z = w.payload.ballot  OBVIOUS
    <3>2. w \in U /\ CIsProposal(w)  BY <3>1, <2>PxEq
    <3>3. w \in CMessages  BY <3>2, <1>Usub
    <3>4. w \in CTran(w)  BY <3>3, CMessagesSubMC, CSelfInTran
    <3>5. \A zz \in CTran(w) : CWellFormed(zz)  BY <3>3 DEF CMessages
    <3>6. CWellFormed(w)  BY <3>4, <3>5
    <3>7. CFilterOut(w)  BY <3>6 DEF CWellFormed
    <3>8. CIsProposal(w) => CB(w) = w.payload.ballot  BY <3>7 DEF CFilterOut
    <3>9. w.payload.ballot = CB(w)  BY <3>2, <3>8
    <3>10. CB(w) <= b  BY <3>2, <1>Uball
    <3> QED BY <3>1, <3>9, <3>10
  <2>finImg. IsFiniteSet(ImgSet)
    <3>1. IsFiniteSet(CTran(xrec))  BY <1>xrecMC, CFiniteTran
    <3>2. IsFiniteSet(Px)  BY <3>1, FS_Subset
    <3> QED BY <3>2, FS_Image
  <2>neImg. ImgSet # {}  BY <2>bInImg
  <2>natImg. \A z \in ImgSet : z \in Nat
    <3> SUFFICES ASSUME NEW w \in Px PROVE w.payload.ballot \in Nat  OBVIOUS
    <3>b. w.payload \in CProposal  BY DEF CIsProposal
    <3>c. PICK bb \in Ballots : w.payload = [type |-> "proposal", ballot |-> bb]  BY <3>b DEF CProposal
    <3>d. w.payload.ballot = bb  BY <3>c
    <3>e. bb \in Nat  BY DEF Ballots
    <3> QED BY <3>d, <3>e
  <2>maxprops. Max(ImgSet) \in ImgSet /\ (\A y \in ImgSet : Max(ImgSet) >= y)
    BY <2>finImg, <2>neImg, <2>natImg, MaxProps
  <2>maxNat. Max(ImgSet) \in Nat  BY <2>maxprops, <2>natImg
  <2>maxIsB. Max(ImgSet) = b
    <3>1. Max(ImgSet) <= b  BY <2>maxprops, <2>ub
    <3>2. Max(ImgSet) >= b  BY <2>maxprops, <2>bInImg
    <3> QED BY <3>1, <3>2, <2>maxNat, <1>bnat
  <2> QED BY <2>maxIsB DEF CB

\* --- CHasDepth(alpha, xrec, k) for every k in 1..d ---
<1>xrecDepth. \A k \in 1..d : CHasDepth(alpha, xrec, k)
  <2> SUFFICES ASSUME NEW k \in 1..d PROVE CHasDepth(alpha, xrec, k)  OBVIOUS
  <2>knat. k \in Nat /\ k >= 1 /\ k <= d  BY <1>dnat
  <2>qd. CCfl(xrec).qd[<<alpha, k>>] = {p \in CTranExcl(xrec) : CB(p) = CB(xrec) /\ CHasDepth(alpha, p, k-1)}
    BY <1>xrecMC, <2>knat, CQdCompute
  <2>qdU. CCfl(xrec).qd[<<alpha, k>>] = {p \in U : CB(p) = b /\ CHasDepth(alpha, p, k-1)}
    BY <2>qd, <1>xrecTEeqU, <1>xrecCB
  <2>k1. k-1 \in 0..(d-1)  BY <2>knat
  <2>quo. CSigS({p \in U : CB(p) = b /\ CHasDepth(alpha, p, k-1)}) \in Quorums(alpha)
    BY <2>k1, <1>downward
  <2>hd. CHasDepth(alpha, xrec, k) = (CSig(xrec) \in Acceptors /\ CSigS(CCfl(xrec).qd[<<alpha,k>>]) \in Quorums(alpha))
    <3>1. k # 0  BY <2>knat
    <3> QED BY <3>1 DEF CHasDepth
  <2> QED BY <2>hd, <1>xrecSig, <2>qdU, <2>quo
<1>xrecHasD. CHasDepth(alpha, xrec, d)  BY <1>xrecDepth, <1>dnat
<1>xrecHas1. CHasDepth(alpha, xrec, 1)  BY <1>xrecDepth, <1>dnat

\* --- xrec is a TwoA ---
<1>xrecTwoA. CIsTwoA(xrec)  BY <1>xrecNotProp, <1>xrecHas1 DEF CIsTwoA

\* --- xrec.priors = CRefs(xrec) ---
<1>xrecFilterPriors. xrec.priors = CRefs(xrec)
  <2>1. CRefs(xrec) = {x \in CTranExcl(xrec) : (\A y \in CTranExcl(xrec) : y = x \/ x \notin CTran(y))}
    BY DEF CRefs
  <2>2. CRefs(xrec) = {x \in U : (\A y \in U : y = x \/ x \notin CTran(y))}  BY <2>1, <1>xrecTEeqU
  <2>3. CMMax(U) = {x \in U : \A y \in U : x \notin CTranExcl(y)}  BY DEF CMMax
  <2>4. \A x \in U : (\A y \in U : y = x \/ x \notin CTran(y)) <=> (\A y \in U : x \notin CTranExcl(y))
    <3> SUFFICES ASSUME NEW x \in U
                 PROVE (\A y \in U : y = x \/ x \notin CTran(y)) <=> (\A y \in U : x \notin CTranExcl(y))
      OBVIOUS
    <3>1. ASSUME NEW y \in U PROVE (y = x \/ x \notin CTran(y)) <=> (x \notin CTranExcl(y))
      BY DEF CTranExcl
    <3> QED BY <3>1
  <2>5. CRefs(xrec) = CMMax(U)  BY <2>2, <2>3, <2>4
  <2> QED BY <2>5, <1>xrecPriors
<1>xrecFilterProp. CIsProposal(xrec) => CB(xrec) = xrec.payload.ballot  BY <1>xrecNotProp
<1>xrecFilter. CFilterOut(xrec)  BY <1>xrecFilterProp, <1>xrecFilterPriors DEF CFilterOut

\* --- has-a-proposal ---
<1>xrecHasProp. \E qq \in CTran(xrec) : CIsProposal(qq)
  <2>1. q0 \in CTran(xrec)  BY <1>q0inU, <1>xrecTranSplit
  <2> QED BY <2>1, <1>q0prop

\* --- not caught ---
<1>caughtSResolve. CaughtS(U) = CCaughtS(U)  BY <1>Usub, CCaughtSResolve
<1>abscaughtU. a \notin CaughtS(U)
  <2>1. a \notin CaughtS(TranClosure(m))  OBVIOUS
  <2> QED BY <2>1, <1>tcEq
<1>conccaughtU. a \notin CCaughtS(U)  BY <1>abscaughtU, <1>caughtSResolve
<1>notcaught. a \notin CCaughtS(CTran(xrec))
  <2> SUFFICES ASSUME NEW m1 \in CTran(xrec), NEW m2 \in CTran(xrec), CSig(m1) = a, CSig(m2) = a
               PROVE m1 \in CTran(m2) \/ m2 \in CTran(m1)
    BY DEF CCaughtS
  <2>1. CASE m1 \in U /\ m2 \in U
    <3> SUFFICES ASSUME ~(m1 \in CTran(m2) \/ m2 \in CTran(m1)) PROVE FALSE  OBVIOUS
    <3>1. m1 \notin CTran(m2) /\ m2 \notin CTran(m1)  OBVIOUS
    <3>2. a \in CCaughtS(U)  BY <2>1, <3>1 DEF CCaughtS
    <3> QED BY <3>2, <1>conccaughtU
  <2>2. CASE m1 = xrec
    <3>0. m2 \in U \/ m2 = xrec  BY <1>xrecTranSplit
    <3>1. CASE m2 \in U
      <4>1. m2 \in CTran(xrec)  BY <3>1, <1>xrecTranSplit
      <4> QED BY <2>2, <4>1
    <3>2. CASE m2 = xrec
      <4>1. xrec \in CTran(xrec)  BY <1>xrecMC, CSelfInTran
      <4> QED BY <2>2, <3>2, <4>1
    <3> QED BY <3>0, <3>1, <3>2
  <2>3. CASE m2 = xrec
    <3>0. m1 \in U \/ m1 = xrec  BY <1>xrecTranSplit
    <3>1. CASE m1 \in U
      <4>1. m1 \in CTran(xrec)  BY <3>1, <1>xrecTranSplit
      <4> QED BY <2>3, <4>1
    <3>2. CASE m1 = xrec
      <4>1. xrec \in CTran(xrec)  BY <1>xrecMC, CSelfInTran
      <4> QED BY <2>3, <3>2, <4>1
    <3> QED BY <3>0, <3>1, <3>2
  <2>0. (m1 \in U \/ m1 = xrec) /\ (m2 \in U \/ m2 = xrec)  BY <1>xrecTranSplit
  <2> QED BY <2>0, <2>1, <2>2, <2>3, <1>xrecTranSplit

\* --- CWellFormed(xrec) ---
<1>xrecNotCaughtVac. CSig(xrec) \in Acceptors => CSig(xrec) \notin CCaught(xrec)
  BY <1>xrecSig, <1>notcaught DEF CCaught
<1>xrecDisj. CIsProposal(xrec) \/ CIsOneB(xrec) \/ CIsTwoA(xrec)  BY <1>xrecTwoA
<1>xrecWF. CWellFormed(xrec)
  BY <1>xrecHasProp, <1>xrecNotCaughtVac, <1>xrecDisj, <1>xrecFilter DEF CWellFormed
<1>allWF. \A z \in CTran(xrec) : CWellFormed(z)
  <2> SUFFICES ASSUME NEW z \in CTran(xrec) PROVE CWellFormed(z)  OBVIOUS
  <2>1. CASE z = xrec  BY <2>1, <1>xrecWF
  <2>2. CASE z \in U
    <3>1. z \in CMessages  BY <1>Usub, <2>2
    <3>2. z \in CTran(z)  BY <3>1, CMessagesSubMC, CSelfInTran
    <3>3. \A zz \in CTran(z) : CWellFormed(zz)  BY <3>1 DEF CMessages
    <3> QED BY <3>2, <3>3
  <2> QED BY <1>xrecTranSplit, <2>1, <2>2
<1>xrecInMessages. xrec \in CMessages  BY <1>xrecMC, <1>allWF DEF CMessages

\* --- resolve back to abstract ---
<1>xrecAbsSig. Sig(xrec) = a  BY <1>xrecInMessages, CSigResolve, <1>xrecSig
<1>xrecAbsTran. Tran(xrec) = CTran(xrec)  BY <1>xrecInMessages, CTranResolve
<1>xrecAbsTE. TranExclusive(xrec) = CTranExcl(xrec)
  BY <1>xrecAbsTran DEF TranExclusive, CTranExcl
<1>xrecAbsTE2. TranExclusive(xrec) = TranClosure(m)  BY <1>xrecAbsTE, <1>xrecTEeqU, <1>tcEq
<1>xrecAbsB. B(xrec) = CB(xrec)  BY <1>xrecInMessages, CBResolve
<1>xrecAbsBb. B(xrec) = b  BY <1>xrecAbsB, <1>xrecCB
<1>xrecAbsHasD. HasDepth(alpha, xrec, d) = CHasDepth(alpha, xrec, d)
  BY <1>xrecInMessages, <1>dnat, CHasDepthResolve
<1>xrecAbsHasDd. HasDepth(alpha, xrec, d)  BY <1>xrecAbsHasD, <1>xrecHasD
<1>xrecAbsIsTwoA. IsTwoA(xrec) = CIsTwoA(xrec)  BY <1>xrecInMessages, CIsTwoAResolve
<1>xrecAbsTwoA. IsTwoA(xrec)  BY <1>xrecAbsIsTwoA, <1>xrecTwoA
<1>xrecAbsCaughtS. CaughtS(CTran(xrec)) = CCaughtS(CTran(xrec))
  <2>1. CTran(xrec) \subseteq CMessages  BY <1>xrecInMessages, CMessageTranClosed
  <2> QED BY <2>1, CCaughtSResolve
<1>xrecAbsCaught. Caught(xrec) = CCaughtS(CTran(xrec))
  BY <1>xrecAbsTran, <1>xrecAbsCaughtS DEF Caught
<1>xrecAbsNotCaught. a \notin Caught(xrec)  BY <1>xrecAbsCaught, <1>notcaught
<1> QED
  BY <1>msgeq, <1>xrecInMessages, <1>xrecAbsSig, <1>xrecAbsBb, <1>xrecAbsHasDd,
     <1>xrecAbsNotCaught, <1>xrecAbsTwoA, <1>xrecAbsTE2

\* ===================================================================
\* Capstone: the concrete instantiation CMI satisfies ALL of
\* MessageInterfaceAssumptions, given only the ValueInterface assumptions
\* (implicit) and the two LearnerGraph assumptions that make quorums nonempty.
\* ===================================================================
LEMMA CMessageInterfaceAssumptions ==
  ASSUME MessageInterface = CMI, LearnersMightAgree, ValidLearnerGraphAssumption
  PROVE MessageInterfaceAssumptions
<1>1. TypeOKMessageInterface  BY CTypeOKMessageInterface
<1>2. TranFinite  BY CTranFinite
<1>3. TranTrans  BY CTranTransProof
<1>4. TranAcyclic  BY CTranAcyclic
<1>5. AlwaysAProposal  BY CAlwaysAProposal
<1>6. AlwaysANewProposal  BY CAlwaysANewProposal
<1>7. AlwaysANewOneB  BY CAlwaysANewOneB
<1>8. AlwaysANewTwoA  BY CAlwaysANewTwoA
<1>9. AcceptorsSubsetSenders  BY CAcceptorsSubsetSenders
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9
  DEF MessageInterfaceAssumptions

\* ======================= status =======================
\* All 9 MessageInterfaceAssumptions conjuncts are proved for the CMI
\* instantiation (see CMessageInterfaceAssumptions above):
\*   - Structural (MessageInterface = CMI alone): TypeOKMessageInterface,
\*     TranFinite, TranTrans, TranAcyclic, AlwaysAProposal, AcceptorsSubsetSenders.
\*   - AlwaysANewProposal: fresh CProposal whose priors are the maximal
\*     antichain (CMMax) of TranClosure(m); sender is a non-acceptor
\*     (CProposerSender) so WellFormed's caught-acceptor clause is vacuous.
\*   - AlwaysANewOneB / AlwaysANewTwoA additionally need
\*     LearnersMightAgree /\ ValidLearnerGraphAssumption (quorums nonempty).
\*     Both build a fresh CReply signed by a over TranClosure(m).  HasDepth's
\*     qd is acceptor-filtered (matching CHasDepth), so the TwoA witness's qd
\*     equals the hypothesized quorum set exactly (depth d), and depth 1
\*     (for IsTwoA) follows by downward closure (CDepthDownward).
\* The abstract<->concrete bridge (CCflResolve/CHasDepthResolve/CIsTwoAResolve
\* etc.) transfers each concrete result to the abstract MessageInterface goal.
=============================================================================
