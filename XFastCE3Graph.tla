------------------------- MODULE XFastCE3Graph -------------------------
\* The learner graph for the MaxDepth-3 counterexample to the NEW DecisionFast.
\*
\* Unlike XFastDepth3 (quorums = ALL acceptors, which BLOCKS Byzantine forks
\* and is therefore safe), this graph gives the fork-carrier learners SMALL,
\* Byzantine-forgeable quorums -- while still being valid, condensed, and
\* having MaxDepth(10) = 3.  That combination (depth 3 + forgeable fork
\* quorums + validity) is the real substrate an attack needs; this file
\* machine-checks that such a graph exists.
\*
\*   Acceptors {1,2,3}: 1 honest, 2 and 3 Byzantine.
\*   Learners  {10,20,30,40}.
\*   Union generators  Yf[10]=Yf[20]={1}, Yf[30]={2}, Yf[40]={3}
\*     (so SS({x,y}) = { Yf[x] \cup Yf[y] }; condensation is automatic).
\*   Quorum generators Q(10)=Q(20)={1,2,3}, Q(30)={2,3}, Q(40)={3}
\*     (upward closed).  Note Q(l) = { k \in {1,2,3} : k >= (elt of Yf[l]) }.
\*
\*   Fork quorums are forgeable: a 40-quorum can be {3} alone (Byzantine a3),
\*   a 30-quorum can be {2,3} (Byzantine a2,a3) -- neither needs honest a1.
\*   10 is self-connected iff 1 is uncaught (SS({10}) = {{1}}), so a1 is the
\*   honest node the disagreement rides on.
\*
\*   ConFromCaught(10, C) = {d : ({1} \cup Yf[d]) \cap C = {}}:
\*     C={1,2,3} -> {}          (1 in C kills everything)
\*     C={2,3}   -> {10,20}     (1 out; 30 needs 2 out, 40 needs 3 out)
\*     C={3}     -> {10,20,30}
\*     C={}      -> {10,20,30,40}
\*   Four distinct values on {1,2,3} > {2,3} > {3} > {} => MaxDepth(10) >= 3.
\*
\*   Validity: for any pair {x,y} the larger Yf-acceptor
\*   m = max(elt Yf[x], elt Yf[y]) lies in Yf[x] \cup Yf[y] (the safety-set
\*   generator) AND in Q(x)={>=Yf[x]} AND in Q(y)={>=Yf[y]}, so
\*   s \cap qx \cap qy contains m -- never empty.

EXTENDS LearnerGraphInterface
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE FiniteSetTheorems
LOCAL INSTANCE Sequences
LOCAL INSTANCE SequenceTheorems

YAcc == {1, 2, 3}
YLrn == {10, 20, 30, 40}
Yf   == [l \in YLrn |-> CASE l = 10 -> {1}
                          [] l = 20 -> {1}
                          [] l = 30 -> {2}
                          [] l = 40 -> {3}]
\* the single quorum generator per learner (upward closure taken by Quorums)
Yg   == [l \in YLrn |-> CASE l = 10 -> {1,2,3}
                          [] l = 20 -> {1,2,3}
                          [] l = 30 -> {2,3}
                          [] l = 40 -> {3}]
YPairs == {{pr[1], pr[2]} : pr \in YLrn \X YLrn}
YSS  == [p \in YPairs |-> {UNION {Yf[l] : l \in p}}]
YQ   == [l \in YLrn |-> {Yg[l]}]
YLG  == [learners |-> YLrn, acceptors |-> YAcc, safety_sets |-> YSS, quorums |-> YQ]

\* ===================================================================
\* Field extraction + basic shape
\* ===================================================================

LEMMA YFields ==
  ASSUME LearnerGraphInterface = YLG
  PROVE /\ Learners = YLrn
        /\ Acceptors = YAcc
        /\ SpecifiedSafetySets = YSS
        /\ SpecifiedQuorums = YQ
BY DEF Learners, Acceptors, SpecifiedSafetySets, SpecifiedQuorums, YLG

LEMMA YAccFinite ==
  ASSUME LearnerGraphInterface = YLG
  PROVE IsFiniteSet(Acceptors)
<1>1. Acceptors = {1,2,3}  BY YFields DEF YAcc
<1>2. {1,2,3} = 1..3  OBVIOUS
<1> QED BY <1>1, <1>2, FS_Interval

LEMMA YfType ==
  ASSUME LearnerGraphInterface = YLG, NEW l \in Learners
  PROVE /\ Yf[l] \subseteq Acceptors
        /\ Yf[l] # {}
        /\ IsFiniteSet(Yf[l])
        /\ Yf[l] \in {{1},{2},{3}}
<1>L. Learners = YLrn /\ Acceptors = YAcc  BY YFields
<1>lx. l \in {10,20,30,40}  BY <1>L DEF YLrn
<1>v. Yf[l] \in {{1},{2},{3}}
  <2>1. CASE l = 10  BY <2>1 DEF Yf, YLrn
  <2>2. CASE l = 20  BY <2>2 DEF Yf, YLrn
  <2>3. CASE l = 30  BY <2>3 DEF Yf, YLrn
  <2>4. CASE l = 40  BY <2>4 DEF Yf, YLrn
  <2> QED BY <1>lx, <2>1, <2>2, <2>3, <2>4
<1>1. Yf[l] \subseteq {1,2,3}  BY <1>v
<1>2. Yf[l] # {}  BY <1>v
<1>3. IsFiniteSet(Yf[l])  BY <1>v, FS_Singleton
<1> QED BY <1>1, <1>2, <1>3, <1>v, <1>L DEF YAcc

LEMMA YgType ==
  ASSUME LearnerGraphInterface = YLG, NEW l \in Learners
  PROVE /\ Yg[l] \subseteq Acceptors
        /\ IsFiniteSet(Yg[l])
        /\ Yf[l] \subseteq Yg[l]
<1>L. Learners = YLrn /\ Acceptors = YAcc  BY YFields
<1>lx. l \in {10,20,30,40}  BY <1>L DEF YLrn
<1>v. Yg[l] \in {{1,2,3},{2,3},{3}} /\ Yf[l] \subseteq Yg[l]
  <2>1. CASE l = 10  BY <2>1 DEF Yf, Yg, YLrn
  <2>2. CASE l = 20  BY <2>2 DEF Yf, Yg, YLrn
  <2>3. CASE l = 30  BY <2>3 DEF Yf, Yg, YLrn
  <2>4. CASE l = 40  BY <2>4 DEF Yf, Yg, YLrn
  <2> QED BY <1>lx, <2>1, <2>2, <2>3, <2>4
<1>1. Yg[l] \subseteq {1,2,3}  BY <1>v
<1>2. IsFiniteSet(Yg[l])
  <2>1. {1,2,3} = 1..3  OBVIOUS
  <2> QED BY <1>1, <2>1, FS_Interval, FS_Subset
<1> QED BY <1>1, <1>2, <1>v, <1>L DEF YAcc

LEMMA YPairsEq ==
  ASSUME LearnerGraphInterface = YLG
  PROVE LearnerPairs = YPairs
<1>L. Learners = YLrn  BY YFields
<1>1. LearnerPairs = {{pr[1], pr[2]} : pr \in Learners \X Learners}  BY DEF LearnerPairs
<1> QED BY <1>1, <1>L DEF YPairs

LEMMA YSafetyGen ==
  ASSUME LearnerGraphInterface = YLG, NEW x \in Learners, NEW y \in Learners
  PROVE GetSpecifiedSafetySets({x, y}) = {Yf[x] \cup Yf[y]}
<1>L. Learners = YLrn /\ SpecifiedSafetySets = YSS  BY YFields
<1>p. {x,y} \in YPairs
  <2>1. <<x,y>> \in Learners \X Learners  OBVIOUS
  <2>2. {x,y} = {(<<x,y>>)[1], (<<x,y>>)[2]}  OBVIOUS
  <2> QED BY <2>1, <2>2, <1>L DEF YPairs
<1>dom. {x,y} \in DOMAIN SpecifiedSafetySets  BY <1>p, <1>L DEF YSS
<1>get. GetSpecifiedSafetySets({x,y}) = SpecifiedSafetySets[{x,y}]
  BY <1>dom DEF GetSpecifiedSafetySets
<1>val. SpecifiedSafetySets[{x,y}] = {UNION {Yf[l] : l \in {x,y}}}  BY <1>p, <1>L DEF YSS
<1>un. UNION {Yf[l] : l \in {x,y}} = Yf[x] \cup Yf[y]
  <2>1. {Yf[l] : l \in {x,y}} = {Yf[x], Yf[y]}  OBVIOUS
  <2> QED BY <2>1
<1> QED BY <1>get, <1>val, <1>un

LEMMA YQuorumGen ==
  ASSUME LearnerGraphInterface = YLG, NEW l \in Learners
  PROVE GetSpecifiedQuorums(l) = {Yg[l]}
<1>L. Learners = YLrn /\ SpecifiedQuorums = YQ  BY YFields
<1>dom. l \in DOMAIN SpecifiedQuorums  BY <1>L DEF YQ, YLrn
<1> QED BY <1>dom, <1>L DEF GetSpecifiedQuorums, YQ

\* Each learner's (safety generator, quorum generator) pair is one of three
\* concrete shapes: Yf[l]={a}, Yg[l]={k in {1,2,3} : k>=a}.
LEMMA YfgExplicit ==
  ASSUME LearnerGraphInterface = YLG, NEW l \in Learners
  PROVE \/ (Yf[l] = {1} /\ Yg[l] = {1,2,3})
        \/ (Yf[l] = {2} /\ Yg[l] = {2,3})
        \/ (Yf[l] = {3} /\ Yg[l] = {3})
<1>lx. l \in {10,20,30,40}  BY YFields DEF YLrn
<1>1. CASE l = 10  BY <1>1 DEF Yf, Yg, YLrn
<1>2. CASE l = 20  BY <1>2 DEF Yf, Yg, YLrn
<1>3. CASE l = 30  BY <1>3 DEF Yf, Yg, YLrn
<1>4. CASE l = 40  BY <1>4 DEF Yf, Yg, YLrn
<1> QED BY <1>lx, <1>1, <1>2, <1>3, <1>4

\* ===================================================================
\* Condensation (union generators, exactly as XFastDepth3)
\* ===================================================================

LEMMA YCondensed ==
  ASSUME LearnerGraphInterface = YLG
  PROVE CondensedLearnerGraphAssumption
<1> SUFFICES ASSUME NEW x \in Learners, NEW y \in Learners, NEW z \in Learners,
                    NEW xy \in SafetySets({x,y}), NEW yz \in SafetySets({y,z})
             PROVE (xy \cup yz) \in SafetySets({x,z})
  BY DEF CondensedLearnerGraphAssumption
<1>gxy. (Yf[x] \cup Yf[y]) \subseteq xy /\ xy \subseteq Acceptors
  <2>1. GetSpecifiedSafetySets({x,y}) = {Yf[x] \cup Yf[y]}  BY YSafetyGen
  <2> QED BY <2>1 DEF SafetySets
<1>gyz. (Yf[y] \cup Yf[z]) \subseteq yz /\ yz \subseteq Acceptors
  <2>1. GetSpecifiedSafetySets({y,z}) = {Yf[y] \cup Yf[z]}  BY YSafetyGen
  <2> QED BY <2>1 DEF SafetySets
<1>gxz. GetSpecifiedSafetySets({x,z}) = {Yf[x] \cup Yf[z]}  BY YSafetyGen
<1>sub. (Yf[x] \cup Yf[z]) \subseteq (xy \cup yz)  BY <1>gxy, <1>gyz
<1>subA. (xy \cup yz) \subseteq Acceptors  BY <1>gxy, <1>gyz
<1>fin. IsFiniteSet(xy \cup yz)
  <2>1. IsFiniteSet(Acceptors)  BY YAccFinite
  <2> QED BY <2>1, <1>subA, FS_Subset
<1> QED BY <1>gxz, <1>sub, <1>subA, <1>fin DEF SafetySets

\* ===================================================================
\* Validity (the NEW hard part: small quorums, shared larger acceptor)
\* ===================================================================

LEMMA YValid ==
  ASSUME LearnerGraphInterface = YLG
  PROVE ValidLearnerGraphAssumption
<1>L. Learners = YLrn /\ Acceptors = YAcc  BY YFields
<1> SUFFICES ASSUME NEW x \in Learners, NEW y \in Learners,
                    NEW s \in SafetySets({x,y}), NEW qx \in Quorums(x), NEW qy \in Quorums(y)
             PROVE (s \cap qx \cap qy) # {}
  BY DEF ValidLearnerGraphAssumption
<1>sgen. GetSpecifiedSafetySets({x,y}) = {Yf[x] \cup Yf[y]}  BY YSafetyGen
<1>ss. (Yf[x] \cup Yf[y]) \subseteq s  BY <1>sgen DEF SafetySets
<1>qxg. Yg[x] \subseteq qx
  <2>1. GetSpecifiedQuorums(x) = {Yg[x]}  BY YQuorumGen
  <2> QED BY <2>1 DEF Quorums
<1>qyg. Yg[y] \subseteq qy
  <2>1. GetSpecifiedQuorums(y) = {Yg[y]}  BY YQuorumGen
  <2> QED BY <2>1 DEF Quorums
\* the larger Yf-acceptor is in the generator AND both quorum generators
\* KEY: for either learner the (Yf, Yg) pair is one of three concrete shapes;
\* across the 9 combinations the larger acceptor lies in the union AND in both
\* quorum generators, so s \cap qx \cap qy is nonempty.
<1>fx. \/ (Yf[x] = {1} /\ Yg[x] = {1,2,3})
       \/ (Yf[x] = {2} /\ Yg[x] = {2,3})
       \/ (Yf[x] = {3} /\ Yg[x] = {3})  BY YfgExplicit
<1>fy. \/ (Yf[y] = {1} /\ Yg[y] = {1,2,3})
       \/ (Yf[y] = {2} /\ Yg[y] = {2,3})
       \/ (Yf[y] = {3} /\ Yg[y] = {3})  BY YfgExplicit
<1>witness. \E a \in (Yf[x] \cup Yf[y]) : a \in Yg[x] /\ a \in Yg[y]
  BY <1>fx, <1>fy
<1> QED BY <1>witness, <1>ss, <1>qxg, <1>qyg

\* ===================================================================
\* Full assumption bundle
\* ===================================================================

LEMMA YLearnerGraphAssumptions ==
  ASSUME LearnerGraphInterface = YLG
  PROVE LearnerGraphAssumptions
<1>L. Learners = YLrn /\ Acceptors = YAcc /\ SpecifiedSafetySets = YSS /\ SpecifiedQuorums = YQ
  BY YFields
<1>t1. SafetySetsTypeOK
  <2>rng. \A p \in YPairs : YSS[p] \in SUBSET (SUBSET Acceptors)
    <3> SUFFICES ASSUME NEW p \in YPairs PROVE YSS[p] \in SUBSET (SUBSET Acceptors)  OBVIOUS
    <3>1. YSS[p] = {UNION {Yf[l] : l \in p}}  BY DEF YSS
    <3>2. UNION {Yf[l] : l \in p} \subseteq Acceptors
      <4> SUFFICES ASSUME NEW a \in UNION {Yf[l] : l \in p} PROVE a \in Acceptors  OBVIOUS
      <4>1. PICK ll \in p : a \in Yf[ll]  OBVIOUS
      <4>2. ll \in Learners
        <5>1. PICK pr \in YLrn \X YLrn : p = {pr[1], pr[2]}  BY DEF YPairs
        <5> QED BY <4>1, <5>1, <1>L DEF YLrn
      <4> QED BY <4>1, <4>2, YfType
    <3> QED BY <3>1, <3>2
  <2>fcn. YSS \in [YPairs -> SUBSET (SUBSET Acceptors)]  BY <2>rng DEF YSS
  <2>eq. YSS \in [LearnerPairs -> SUBSET (SUBSET Acceptors)]  BY <2>fcn, YPairsEq
  <2> QED BY <2>eq, <1>L DEF SafetySetsTypeOK
<1>t2. QuorumsTypeOK
  <2>rng. \A l \in YLrn : YQ[l] \in SUBSET (SUBSET Acceptors)
    <3> SUFFICES ASSUME NEW l \in YLrn PROVE YQ[l] \in SUBSET (SUBSET Acceptors)  OBVIOUS
    <3>1. YQ[l] = {Yg[l]}  BY DEF YQ
    <3>2. Yg[l] \subseteq Acceptors  BY YgType, <1>L
    <3> QED BY <3>1, <3>2
  <2>fcn. YQ \in [YLrn -> SUBSET (SUBSET Acceptors)]  BY <2>rng DEF YQ
  <2> QED BY <2>fcn, <1>L DEF QuorumsTypeOK
<1>t3. FiniteAcceptors  BY YAccFinite DEF FiniteAcceptors
<1>t4. FiniteLearners
  <2>1. Learners = {10,20,30,40}  BY <1>L DEF YLrn
  <2>2. {10,20,30,40} = {10} \cup ({20} \cup ({30} \cup {40}))  OBVIOUS
  <2> QED BY <2>1, <2>2, FS_Singleton, FS_Union DEF FiniteLearners
<1>t5. LearnersNonEmpty  BY <1>L DEF LearnersNonEmpty, YLrn
<1>t6. QuorumsNonEmpty
  <2> SUFFICES ASSUME NEW l \in Learners PROVE Quorums(l) # {}  BY DEF QuorumsNonEmpty
  <2>1. GetSpecifiedQuorums(l) = {Yg[l]}  BY YQuorumGen
  <2>2. Yg[l] \in SUBSET Acceptors /\ IsFiniteSet(Yg[l]) /\ Yg[l] \subseteq Yg[l]  BY YgType
  <2>3. Yg[l] \in Quorums(l)  BY <2>1, <2>2 DEF Quorums
  <2> QED BY <2>3
<1>t7. LearnersMightAgree
  <2> SUFFICES ASSUME NEW p \in LearnerPairs PROVE Acceptors \in SafetySets(p)
    BY DEF LearnersMightAgree
  <2>pe. p \in YPairs  BY YPairsEq
  <2>xy. PICK x, y : x \in Learners /\ y \in Learners /\ p = {x,y}
    <3>1. PICK pr \in YLrn \X YLrn : p = {pr[1], pr[2]}  BY <2>pe DEF YPairs
    <3> QED BY <3>1, <1>L DEF YLrn
  <2>gen. GetSpecifiedSafetySets(p) = {Yf[x] \cup Yf[y]}  BY <2>xy, YSafetyGen
  <2>sub. (Yf[x] \cup Yf[y]) \subseteq Acceptors
    <3>1. Yf[x] \subseteq Acceptors /\ Yf[y] \subseteq Acceptors  BY <2>xy, YfType
    <3> QED BY <3>1
  <2> QED BY <2>gen, <2>sub, YAccFinite DEF SafetySets
<1>t8. CondensedLearnerGraphAssumption  BY YCondensed
<1>t9. ValidLearnerGraphAssumption  BY YValid
<1> QED BY <1>t1, <1>t2, <1>t3, <1>t4, <1>t5, <1>t6, <1>t7, <1>t8, <1>t9
       DEF LearnerGraphAssumptions

\* ===================================================================
\* ConFromCaught evaluation + MaxDepth(10) >= 3
\* ===================================================================

LEMMA YConMember ==
  ASSUME LearnerGraphInterface = YLG, NEW b \in Learners, NEW C
  PROVE b \in ConFromCaught(10, C) <=> (Yf[10] \cup Yf[b]) \cap C = {}
<1>L. Learners = YLrn  BY YFields
<1>10L. 10 \in Learners  BY <1>L DEF YLrn
<1>gen. GetSpecifiedSafetySets({10, b}) = {Yf[10] \cup Yf[b]}  BY <1>10L, YSafetyGen
<1>ss. SafetySets({10,b})
       = {s \in SUBSET Acceptors : IsFiniteSet(s) /\ (Yf[10] \cup Yf[b]) \subseteq s}
  BY <1>gen DEF SafetySets
<1>fgen. /\ IsFiniteSet(Yf[10] \cup Yf[b])
         /\ (Yf[10] \cup Yf[b]) \subseteq Acceptors
  <2>1. Yf[10] \subseteq Acceptors /\ IsFiniteSet(Yf[10])  BY <1>10L, YfType
  <2>2. Yf[b] \subseteq Acceptors /\ IsFiniteSet(Yf[b])  BY YfType
  <2> QED BY <2>1, <2>2, FS_Union
<1>mem. b \in ConFromCaught(10, C)
        <=> (b \in Learners /\ \E s \in SafetySets({10,b}) : s \cap C = {})
  BY DEF ConFromCaught
<1>1. (\E s \in SafetySets({10,b}) : s \cap C = {}) <=> ((Yf[10] \cup Yf[b]) \cap C = {})
  <2>a. ASSUME (Yf[10] \cup Yf[b]) \cap C = {}
        PROVE \E s \in SafetySets({10,b}) : s \cap C = {}
    <3>1. (Yf[10] \cup Yf[b]) \in SafetySets({10,b})  BY <1>ss, <1>fgen
    <3> QED BY <3>1, <2>a
  <2>b. ASSUME NEW s \in SafetySets({10,b}), s \cap C = {}
        PROVE (Yf[10] \cup Yf[b]) \cap C = {}
    <3>1. (Yf[10] \cup Yf[b]) \subseteq s  BY <2>b, <1>ss
    <3> QED BY <3>1, <2>b
  <2> QED BY <2>a, <2>b
<1> QED BY <1>mem, <1>1, <1>10L, b \in Learners

LEMMA YConChain ==
  ASSUME LearnerGraphInterface = YLG
  PROVE /\ 10 \notin ConFromCaught(10, {1,2,3})
        /\ 10 \in ConFromCaught(10, {2,3})
        /\ 30 \notin ConFromCaught(10, {2,3})
        /\ 30 \in ConFromCaught(10, {3})
        /\ 40 \notin ConFromCaught(10, {3})
        /\ 40 \in ConFromCaught(10, {})
<1>L. Learners = YLrn  BY YFields
<1>10L. 10 \in Learners /\ 30 \in Learners /\ 40 \in Learners  BY <1>L DEF YLrn
<1>f. Yf[10] = {1} /\ Yf[30] = {2} /\ Yf[40] = {3}  BY <1>10L DEF Yf, YLrn
<1>a. 10 \notin ConFromCaught(10, {1,2,3})
  <2>1. (Yf[10] \cup Yf[10]) \cap {1,2,3} # {}  BY <1>f
  <2> QED BY <2>1, <1>10L, YConMember
<1>b. 10 \in ConFromCaught(10, {2,3})
  <2>1. (Yf[10] \cup Yf[10]) \cap {2,3} = {}  BY <1>f
  <2> QED BY <2>1, <1>10L, YConMember
<1>c. 30 \notin ConFromCaught(10, {2,3})
  <2>1. (Yf[10] \cup Yf[30]) \cap {2,3} # {}  BY <1>f
  <2> QED BY <2>1, <1>10L, YConMember
<1>d. 30 \in ConFromCaught(10, {3})
  <2>1. (Yf[10] \cup Yf[30]) \cap {3} = {}  BY <1>f
  <2> QED BY <2>1, <1>10L, YConMember
<1>e. 40 \notin ConFromCaught(10, {3})
  <2>1. (Yf[10] \cup Yf[40]) \cap {3} # {}  BY <1>f
  <2> QED BY <2>1, <1>10L, YConMember
<1>g. 40 \in ConFromCaught(10, {})
  <2>1. (Yf[10] \cup Yf[40]) \cap {} = {}  BY <1>f
  <2> QED BY <2>1, <1>10L, YConMember
<1> QED BY <1>a, <1>b, <1>c, <1>d, <1>e, <1>g

LEMMA YConDistinct ==
  ASSUME LearnerGraphInterface = YLG
  PROVE /\ ConFromCaught(10, {1,2,3}) # ConFromCaught(10, {2,3})
        /\ ConFromCaught(10, {2,3})   # ConFromCaught(10, {3})
        /\ ConFromCaught(10, {3})     # ConFromCaught(10, {})
BY YConChain

YWit == [i \in 1..4 |-> CASE i = 1 -> {1,2,3}
                          [] i = 2 -> {2,3}
                          [] i = 3 -> {3}
                          [] i = 4 -> {}]

LEMMA YWitIsValidSeq ==
  ASSUME LearnerGraphInterface = YLG
  PROVE YWit \in ValidSeqs(10)
<1>acc. Acceptors = {1,2,3}  BY YFields DEF YAcc
<1>vals. YWit[1] = {1,2,3} /\ YWit[2] = {2,3} /\ YWit[3] = {3} /\ YWit[4] = {}
  BY DEF YWit
<1>fcn. YWit \in [1..4 -> SUBSET Acceptors]
  <2> SUFFICES ASSUME NEW i \in 1..4 PROVE YWit[i] \in SUBSET Acceptors  BY DEF YWit
  <2>1. YWit[i] \in {{1,2,3},{2,3},{3},{}}  BY DEF YWit
  <2> QED BY <2>1, <1>acc
<1>seq. YWit \in Seq(SUBSET Acceptors)
  <2>1. 4 \in Nat  OBVIOUS
  <2> QED BY <1>fcn, <2>1, SeqDef
<1>len. Len(YWit) = 4
  <2>1. DOMAIN YWit = 1..Len(YWit) /\ Len(YWit) \in Nat  BY <1>seq, LenProperties
  <2>2. DOMAIN YWit = 1..4  BY DEF YWit
  <2> QED BY <2>1, <2>2
<1>chain. \A i \in 1..(Len(YWit)-1) :
             YWit[i+1] \subseteq YWit[i]
             /\ ConFromCaught(10, YWit[i]) # ConFromCaught(10, YWit[i+1])
  <2> SUFFICES ASSUME NEW i \in 1..3
               PROVE YWit[i+1] \subseteq YWit[i]
                     /\ ConFromCaught(10, YWit[i]) # ConFromCaught(10, YWit[i+1])
    BY <1>len
  <2>1. CASE i = 1  BY <2>1, <1>vals, YConDistinct
  <2>2. CASE i = 2  BY <2>2, <1>vals, YConDistinct
  <2>3. CASE i = 3  BY <2>3, <1>vals, YConDistinct
  <2> QED BY <2>1, <2>2, <2>3
<1> QED BY <1>seq, <1>chain DEF ValidSeqs

LEMMA MaxDepthLowerBound ==
  ASSUME FiniteAcceptors, NEW alpha \in Learners, NEW k \in Nat,
         NEW l \in ValidSeqs(alpha), Len(l) = k + 1
  PROVE MaxDepth(alpha) >= k
<1> DEFINE D == {Len(s) - 1 : s \in ValidSeqs(alpha)}
<1> DEFINE LL == {Len(s) : s \in ValidSeqs(alpha)}
<1>accfin. IsFiniteSet(Acceptors)  BY DEF FiniteAcceptors
<1>cardnat. Cardinality(Acceptors) \in Nat  BY <1>accfin, FS_CardinalityType
<1>bound. \A s \in ValidSeqs(alpha) : Len(s) <= Cardinality(Acceptors) + 1
  <2> SUFFICES ASSUME NEW s \in ValidSeqs(alpha) PROVE Len(s) <= Cardinality(Acceptors) + 1  OBVIOUS
  <2> QED BY ValidSeqLenBoundAcceptors
<1>Lsub. LL \subseteq 0..(Cardinality(Acceptors)+1)
  <2> SUFFICES ASSUME NEW n \in LL PROVE n \in 0..(Cardinality(Acceptors)+1)  OBVIOUS
  <2>1. PICK s \in ValidSeqs(alpha) : n = Len(s)  OBVIOUS
  <2>2. Len(s) \in Nat  BY <2>1 DEF ValidSeqs
  <2>3. Len(s) <= Cardinality(Acceptors)+1  BY <2>1, <1>bound
  <2> QED BY <2>1, <2>2, <2>3
<1>rangefin. IsFiniteSet(0..(Cardinality(Acceptors)+1))  BY <1>cardnat, FS_Interval
<1>Lfin. IsFiniteSet(LL)  BY <1>Lsub, <1>rangefin, FS_Subset
<1>lIn. Len(l) \in LL  OBVIOUS
<1>Lne. LL # {}  BY <1>lIn
<1>Lnat. \A xx \in LL : xx \in Nat  BY <1>Lsub
<1>maxprops. Max(LL) \in LL /\ (\A y \in LL : Max(LL) >= y)  BY <1>Lfin, <1>Lne, <1>Lnat, MaxProps
<1>MaxLnat. Max(LL) \in Nat  BY <1>maxprops, <1>Lnat
<1>dwit. Max(LL) - 1 \in D
  <2>1. PICK s \in ValidSeqs(alpha) : Len(s) = Max(LL)  BY <1>maxprops
  <2> QED BY <2>1
<1>dupper. \A d \in D : d <= Max(LL) - 1
  <2> SUFFICES ASSUME NEW d \in D PROVE d <= Max(LL)-1  OBVIOUS
  <2>1. PICK s \in ValidSeqs(alpha) : d = Len(s)-1  OBVIOUS
  <2>2. Len(s) \in LL  BY <2>1
  <2>3. Len(s) <= Max(LL)  BY <2>2, <1>maxprops
  <2>4. Len(s) \in Nat  BY <2>1 DEF ValidSeqs
  <2> QED BY <2>1, <2>3, <2>4, <1>MaxLnat
<1>witness. \E xx \in D : \A y \in D : xx >= y  BY <1>dwit, <1>dupper
<1>maxprops2. MaxDepth(alpha) \in D /\ (\A y \in D : MaxDepth(alpha) >= y)
  BY <1>witness DEF MaxDepth, Max
<1>kInD. k \in D
  <2>1. Len(l) - 1 = k  OBVIOUS
  <2>2. Len(l) - 1 \in D  OBVIOUS
  <2> QED BY <2>1, <2>2
<1> QED BY <1>maxprops2, <1>kInD

THEOREM YMaxDepthGE3 ==
  ASSUME LearnerGraphInterface = YLG
  PROVE MaxDepth(10) >= 3
<1>fa. FiniteAcceptors  BY YAccFinite DEF FiniteAcceptors
<1>10L. 10 \in Learners  BY YFields DEF YLrn
<1>wit. YWit \in ValidSeqs(10)  BY YWitIsValidSeq
<1>len. Len(YWit) = 3 + 1  BY DEF YWit
<1>3nat. 3 \in Nat  OBVIOUS
<1> QED BY <1>fa, <1>10L, <1>3nat, <1>wit, <1>len, MaxDepthLowerBound

====================================================================
