--------------------------- MODULE CWellFormedSameTE ---------------------------
\* Well-formedness of a non-proposal record is determined by its sender and
\* its strict closure alone -- the priors field itself does not matter.  Every
\* CWellFormed conjunct reads the record only through CTran = {self} \cup T,
\* CSig, CB (max over T's proposals, the record being none), the same-ballot
\* count over {self} \cup T (both selves count once), the collapsed caught set
\* CCaughtS(T) (a pair involving the record itself never passes the
\* incomparability test), and the level-1 Qd set over T (CQdCompute).  This is
\* what lets ANY abstract forced-send witness certify the well-formedness of
\* the canonical candidate, now that witnesses are not unique.
EXTENDS MessageConcrete, CBuiltTran, CBuiltInCMC, CUnionTranFiniteClosed,
        CQdCompute, FiniteSetTheorems
LOCAL INSTANCE TLAPS

LEMMA CWellFormedSameTE ==
  ASSUME NEW sdr \in CSenders, NEW pl \in CPayload, pl \notin CProposal,
         NEW pr1, pr1 \subseteq CMessages, IsFiniteSet(pr1),
         NEW pr2, pr2 \subseteq CMessages, IsFiniteSet(pr2),
         UNION {CTran(p) : p \in pr1} = UNION {CTran(p) : p \in pr2},
         CWellFormed([sender |-> sdr, payload |-> pl, priors |-> pr1])
  PROVE  CWellFormed([sender |-> sdr, payload |-> pl, priors |-> pr2])
<1> DEFINE a == [sender |-> sdr, payload |-> pl, priors |-> pr1]
<1> DEFINE b == [sender |-> sdr, payload |-> pl, priors |-> pr2]
<1> DEFINE T == UNION {CTran(p) : p \in pr1}
<1>tra. CTran(a) = {a} \cup T /\ CTranExcl(a) = T
  BY CBuiltTran
<1>trb. CTran(b) = {b} \cup T /\ CTranExcl(b) = T
  <2>1. CTran(b) = {b} \cup UNION {CTran(p) : p \in pr2}
          /\ CTranExcl(b) = UNION {CTran(p) : p \in pr2}
    BY CBuiltTran
  <2> QED BY <2>1
<1>anot. a \notin T  BY <1>tra DEF CTranExcl
<1>bnot. b \notin T  BY <1>trb DEF CTranExcl
<1>pa. ~CIsProposal(a) /\ ~CIsProposal(b)  BY DEF CIsProposal
<1>amc. a \in CMC  BY CBuiltInCMC
<1>bmc. b \in CMC  BY CBuiltInCMC
<1>tfin. IsFiniteSet(T)  BY CUnionTranFiniteClosed
<1>sig. CSig(a) = sdr /\ CSig(b) = sdr  BY DEF CSig
<1>props. /\ {w \in CTran(a) : CIsProposal(w)} = {w \in T : CIsProposal(w)}
          /\ {w \in CTran(b) : CIsProposal(w)} = {w \in T : CIsProposal(w)}
  BY <1>tra, <1>trb, <1>pa
<1>cb. CB(a) = CB(b)
  <2>1. {w.payload.ballot : w \in {y \in CTran(a) : CIsProposal(y)}}
          = {w.payload.ballot : w \in {y \in CTran(b) : CIsProposal(y)}}
    BY <1>props
  <2> QED BY <2>1 DEF CB
<1>c1. (\E z \in CTran(a) : CIsProposal(z)) <=> (\E z \in CTran(b) : CIsProposal(z))
  <2>1. (\E z \in CTran(a) : CIsProposal(z))
          <=> {w \in CTran(a) : CIsProposal(w)} # {}
    OBVIOUS
  <2>2. (\E z \in CTran(b) : CIsProposal(z))
          <=> {w \in CTran(b) : CIsProposal(w)} # {}
    OBVIOUS
  <2> QED BY <2>1, <2>2, <1>props
<1>collapse. \A z, TT : CTran(z) = {z} \cup TT =>
               CCaughtS({z} \cup TT) = CCaughtS(TT)
  <2> SUFFICES ASSUME NEW z, NEW TT, CTran(z) = {z} \cup TT
      PROVE CCaughtS({z} \cup TT) = CCaughtS(TT)
    OBVIOUS
  <2>sup. CCaughtS(TT) \subseteq CCaughtS({z} \cup TT)
    <3> SUFFICES ASSUME NEW aa \in CCaughtS(TT)
        PROVE aa \in CCaughtS({z} \cup TT)  OBVIOUS
    <3>1. PICK m1 \in TT, m2 \in TT :
            /\ CSig(m1) = aa /\ CSig(m2) = aa
            /\ m1 \notin CTran(m2) /\ m2 \notin CTran(m1)
      BY DEF CCaughtS
    <3>2. aa \in Acceptors  BY DEF CCaughtS
    <3> QED BY <3>1, <3>2 DEF CCaughtS
  <2>sub. CCaughtS({z} \cup TT) \subseteq CCaughtS(TT)
    <3> SUFFICES ASSUME NEW aa \in CCaughtS({z} \cup TT)
        PROVE aa \in CCaughtS(TT)  OBVIOUS
    <3>1. PICK m1 \in {z} \cup TT : \E m2 \in {z} \cup TT :
            /\ CSig(m1) = aa /\ CSig(m2) = aa
            /\ m1 \notin CTran(m2) /\ m2 \notin CTran(m1)
      BY DEF CCaughtS
    <3>2. PICK m2 \in {z} \cup TT :
            /\ CSig(m1) = aa /\ CSig(m2) = aa
            /\ m1 \notin CTran(m2) /\ m2 \notin CTran(m1)
      BY <3>1
    <3>3. aa \in Acceptors  BY DEF CCaughtS
    <3>m1. m1 # z
      <4>1. CASE m1 = z
        <5>1. m2 \in CTran(m1)  BY <4>1
        <5> QED BY <5>1, <3>2
      <4> QED BY <4>1
    <3>m2. m2 # z
      <4>1. CASE m2 = z
        <5>1. m1 \in CTran(m2)  BY <4>1
        <5> QED BY <5>1, <3>2
      <4> QED BY <4>1
    <3>4. m1 \in TT /\ m2 \in TT  BY <3>m1, <3>m2
    <3> QED BY <3>2, <3>3, <3>4 DEF CCaughtS
  <2> QED BY <2>sub, <2>sup
<1>ca. CCaught(a) = CCaughtS(T)
  <2>1. CCaught(a) = CCaughtS({a} \cup T)  BY <1>tra DEF CCaught
  <2>2. CCaughtS({a} \cup T) = CCaughtS(T)  BY <1>tra, <1>collapse
  <2> QED BY <2>1, <2>2
<1>cbt. CCaught(b) = CCaughtS(T)
  <2>1. CCaught(b) = CCaughtS({b} \cup T)  BY <1>trb DEF CCaught
  <2>2. CCaughtS({b} \cup T) = CCaughtS(T)  BY <1>trb, <1>collapse
  <2> QED BY <2>1, <2>2
<1>c2. (CSig(a) \in Acceptors => CSig(a) \notin CCaught(a))
         <=> (CSig(b) \in Acceptors => CSig(b) \notin CCaught(b))
  BY <1>ca, <1>cbt, <1>sig
<1> DEFINE St == {w \in T : CB(w) = CB(a)}
<1>sa. {w \in CTran(a) : CB(w) = CB(a)} = {a} \cup St
  <2>sub. {w \in CTran(a) : CB(w) = CB(a)} \subseteq {a} \cup St
    <3> SUFFICES ASSUME NEW w \in CTran(a), CB(w) = CB(a)
        PROVE w \in {a} \cup St  OBVIOUS
    <3>1. w \in {a} \cup T  BY <1>tra
    <3> QED BY <3>1
  <2>sup. {a} \cup St \subseteq {w \in CTran(a) : CB(w) = CB(a)}
    <3>1. a \in CTran(a)  BY <1>tra
    <3>2. St \subseteq CTran(a)  BY <1>tra
    <3> QED BY <3>1, <3>2
  <2> QED BY <2>sub, <2>sup
<1>sb. {w \in CTran(b) : CB(w) = CB(b)} = {b} \cup St
  <2>sub. {w \in CTran(b) : CB(w) = CB(b)} \subseteq {b} \cup St
    <3> SUFFICES ASSUME NEW w \in CTran(b), CB(w) = CB(b)
        PROVE w \in {b} \cup St  OBVIOUS
    <3>1. w \in {b} \cup T  BY <1>trb
    <3> QED BY <3>1, <1>cb
  <2>sup. {b} \cup St \subseteq {w \in CTran(b) : CB(w) = CB(b)}
    <3>1. b \in CTran(b)  BY <1>trb
    <3>2. St \subseteq CTran(b)  BY <1>trb
    <3> QED BY <3>1, <3>2, <1>cb
  <2> QED BY <2>sub, <2>sup
<1>stfin. IsFiniteSet(St)  BY <1>tfin, FS_Subset
<1>card. Cardinality({a} \cup St) = Cardinality({b} \cup St)
  <2>1. a \notin St /\ b \notin St  BY <1>anot, <1>bnot
  <2>2. {a} \cup St = St \cup {a} /\ {b} \cup St = St \cup {b}  OBVIOUS
  <2>3. Cardinality(St \cup {a}) = Cardinality(St) + 1
    BY <1>stfin, <2>1, FS_AddElement
  <2>4. Cardinality(St \cup {b}) = Cardinality(St) + 1
    BY <1>stfin, <2>1, FS_AddElement
  <2> QED BY <2>2, <2>3, <2>4
<1>c3one. CIsOneB(a) <=> CIsOneB(b)
  <2>1. Cardinality({w \in CTran(a) : CB(w) = CB(a)})
          = Cardinality({w \in CTran(b) : CB(w) = CB(b)})
    BY <1>sa, <1>sb, <1>card
  <2> QED BY <2>1, <1>pa DEF CIsOneB
<1>ar. 1 \in Nat /\ 1 >= 1 /\ 1 # 0  BY SMT
<1>qd. \A alpha \in Learners :
         CCfl(a).qd[<<alpha, 1>>] = CCfl(b).qd[<<alpha, 1>>]
  <2> SUFFICES ASSUME NEW alpha \in Learners
      PROVE CCfl(a).qd[<<alpha, 1>>] = CCfl(b).qd[<<alpha, 1>>]  OBVIOUS
  <2>1. CCfl(a).qd[<<alpha, 1>>]
          = {p \in CTranExcl(a) : CB(p) = CB(a) /\ CHasDepth(alpha, p, 1-1)}
    BY <1>amc, <1>ar, CQdCompute
  <2>2. CCfl(b).qd[<<alpha, 1>>]
          = {p \in CTranExcl(b) : CB(p) = CB(b) /\ CHasDepth(alpha, p, 1-1)}
    BY <1>bmc, <1>ar, CQdCompute
  <2>3. {p \in CTranExcl(a) : CB(p) = CB(a) /\ CHasDepth(alpha, p, 1-1)}
          = {p \in CTranExcl(b) : CB(p) = CB(b) /\ CHasDepth(alpha, p, 1-1)}
    BY <1>tra, <1>trb, <1>cb
  <2> QED BY <2>1, <2>2, <2>3
<1>c3two. CIsTwoA(a) <=> CIsTwoA(b)
  <2>hd. \A alpha \in Learners :
           CHasDepth(alpha, a, 1) <=> CHasDepth(alpha, b, 1)
    <3> SUFFICES ASSUME NEW alpha \in Learners
        PROVE CHasDepth(alpha, a, 1) <=> CHasDepth(alpha, b, 1)  OBVIOUS
    <3>1. CHasDepth(alpha, a, 1)
            = (/\ CSig(a) \in Acceptors
               /\ CSigS(CCfl(a).qd[<<alpha, 1>>]) \in Quorums(alpha))
      BY <1>ar DEF CHasDepth
    <3>2. CHasDepth(alpha, b, 1)
            = (/\ CSig(b) \in Acceptors
               /\ CSigS(CCfl(b).qd[<<alpha, 1>>]) \in Quorums(alpha))
      BY <1>ar DEF CHasDepth
    <3>3. CSigS(CCfl(a).qd[<<alpha, 1>>]) = CSigS(CCfl(b).qd[<<alpha, 1>>])
      BY <1>qd
    <3> QED BY <3>1, <3>2, <3>3, <1>sig
  <2> QED BY <2>hd, <1>pa DEF CIsTwoA
<1>wfa. /\ \E z \in CTran(a) : CIsProposal(z)
        /\ CSig(a) \in Acceptors => CSig(a) \notin CCaught(a)
        /\ CIsProposal(a) \/ CIsOneB(a) \/ CIsTwoA(a)
        /\ CFilterOut(a)
  BY DEF CWellFormed
<1>fob. CFilterOut(b)  BY <1>pa DEF CFilterOut
<1> QED
  BY <1>wfa, <1>c1, <1>c2, <1>c3one, <1>c3two, <1>pa, <1>fob
  DEF CWellFormed
=============================================================================
