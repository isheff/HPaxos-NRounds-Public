-------------- MODULE LiveAcceptorsSentDepthBallotDecision --------------
EXTENDS HPaxosPlusCal, FiniteSetTheorems,
        TranClosureExpanding, QuorumUpward, FiniteDiamond
LOCAL INSTANCE TLAPS

LEMMA LiveAcceptorsSentDepthBallotDecision ==
  ASSUME MessageInterfaceAssumptions, ValueInterfaceAssumptions, LearnerGraphAssumptions,
         AcceptorsAssumptions,
         NEW alpha \in Learners, NEW allmessages \in SUBSET Messages, NEW b \in Ballots,
         LiveAcceptors \in Quorums(alpha),
         LiveAcceptorsSentDepthBallot(allmessages, alpha, b, MaxDepth(alpha))
  PROVE  Spec => (IsAllMessagesEverSent(allmessages) => <>Decision(Msgs, alpha, b))
<1>fa. IsFiniteSet(Acceptors)  BY DEF LearnerGraphAssumptions, FiniteAcceptors
<1>lsub. LiveAcceptors \subseteq Acceptors
  BY DEF AcceptorsAssumptions, SafeAcceptorsAssumption, LiveAcceptorsAssumption
<1>lfin. IsFiniteSet(LiveAcceptors)  BY <1>lsub, <1>fa, FS_Subset
<1>ldsb. LiveAcceptors \subseteq SigS({x \in allmessages : B(x) = b /\ HasDepth(alpha, x, MaxDepth(alpha))})
  BY DEF LiveAcceptorsSentDepthBallot
<1> DEFINE ch(aa) == CHOOSE x \in allmessages : (Sig(x)=aa /\ B(x)=b /\ HasDepth(alpha,x,MaxDepth(alpha)))
<1> DEFINE W == {ch(aa) : aa \in LiveAcceptors}
<1>ch. \A aa \in LiveAcceptors :
         ch(aa) \in allmessages /\ Sig(ch(aa))=aa /\ B(ch(aa))=b /\ HasDepth(alpha,ch(aa),MaxDepth(alpha))
  <2> SUFFICES ASSUME NEW aa \in LiveAcceptors
               PROVE  ch(aa) \in allmessages /\ Sig(ch(aa))=aa /\ B(ch(aa))=b /\ HasDepth(alpha,ch(aa),MaxDepth(alpha))
    OBVIOUS
  <2>ne. \E x \in allmessages : (Sig(x)=aa /\ B(x)=b /\ HasDepth(alpha,x,MaxDepth(alpha)))  BY <1>ldsb DEF SigS
  <2> QED  BY <2>ne
<1>wshape. \A w \in W : B(w)=b /\ HasDepth(alpha,w,MaxDepth(alpha)) /\ Sig(w) \in Acceptors
  <2> SUFFICES ASSUME NEW w \in W PROVE B(w)=b /\ HasDepth(alpha,w,MaxDepth(alpha)) /\ Sig(w) \in Acceptors  OBVIOUS
  <2>1. PICK aa \in LiveAcceptors : w = ch(aa)  OBVIOUS
  <2>2. B(w)=b /\ HasDepth(alpha,w,MaxDepth(alpha)) /\ Sig(w)=aa  BY <2>1, <1>ch
  <2>3. aa \in Acceptors  BY <1>lsub
  <2> QED  BY <2>2, <2>3
<1>wsig. \A aa \in LiveAcceptors : \E w \in W : Sig(w) = aa
  <2> SUFFICES ASSUME NEW aa \in LiveAcceptors PROVE \E w \in W : Sig(w) = aa  OBVIOUS
  <2>w. ch(aa) \in W  OBVIOUS
  <2>s. Sig(ch(aa)) = aa  BY <1>ch
  <2> QED  BY <2>w, <2>s
<1>wsub. W \subseteq allmessages  BY <1>ch
<1>wfin. IsFiniteSet(W)  BY <1>lfin, FS_Image
\* --- necessitate  W subseteq Msgs => Decision(Msgs,alpha,b)  (Spec in goal) ---
<1>1. Init => (W \subseteq Msgs => Decision(Msgs, alpha, b))
  <2> SUFFICES ASSUME W \subseteq Msgs PROVE Decision(Msgs, alpha, b)  OBVIOUS
  <2> DEFINE DS == {x \in TranClosure(Msgs) : B(x)=b /\ HasDepth(alpha,x,MaxDepth(alpha))}
  <2>ntc. Msgs \subseteq TranClosure(Msgs)  BY TranClosureExpanding
  <2>qs. LiveAcceptors \subseteq SigS(DS)
    <3> SUFFICES ASSUME NEW aa \in LiveAcceptors PROVE aa \in SigS(DS)  OBVIOUS
    <3>1. PICK w \in W : Sig(w)=aa  BY <1>wsig
    <3>2. w \in Msgs  BY <3>1
    <3>3. w \in TranClosure(Msgs)  BY <3>2, <2>ntc
    <3>4. B(w)=b /\ HasDepth(alpha,w,MaxDepth(alpha))  BY <3>1, <1>wshape
    <3>5. w \in DS  BY <3>3, <3>4
    <3> QED  BY <3>5, <3>1 DEF SigS
  <2>acc. SigS(DS) \subseteq Acceptors
    <3> SUFFICES ASSUME NEW aa \in SigS(DS) PROVE aa \in Acceptors  OBVIOUS
    <3>1. PICK ww \in DS : aa = Sig(ww)  BY DEF SigS
    <3>2. HasDepth(alpha, ww, MaxDepth(alpha))  BY <3>1
    <3> QED  BY <3>1, <3>2 DEF HasDepth
  <2>fin. IsFiniteSet(SigS(DS))  BY <2>acc, <1>fa, FS_Subset
  <2>quo. SigS(DS) \in Quorums(alpha)  BY <2>qs, <2>acc, <2>fin, QuorumUpward
  <2> QED  BY <2>quo DEF Decision, DecisionSlow
<1>2. (W \subseteq Msgs => Decision(Msgs, alpha, b)) /\ [Next]_vars
      => (W \subseteq Msgs => Decision(Msgs, alpha, b))'
  <2> SUFFICES ASSUME (W \subseteq Msgs)' PROVE (Decision(Msgs, alpha, b))'  OBVIOUS
  <2>ws2. W \subseteq Msgs'  OBVIOUS
  <2> DEFINE DSp == {x \in TranClosure(Msgs') : B(x)=b /\ HasDepth(alpha,x,MaxDepth(alpha))}
  <2>ntc. Msgs' \subseteq TranClosure(Msgs')  BY TranClosureExpanding
  <2>qs. LiveAcceptors \subseteq SigS(DSp)
    <3> SUFFICES ASSUME NEW aa \in LiveAcceptors PROVE aa \in SigS(DSp)  OBVIOUS
    <3>1. PICK w \in W : Sig(w)=aa  BY <1>wsig
    <3>2. w \in Msgs'  BY <3>1, <2>ws2
    <3>3. w \in TranClosure(Msgs')  BY <3>2, <2>ntc
    <3>4. B(w)=b /\ HasDepth(alpha,w,MaxDepth(alpha))  BY <3>1, <1>wshape
    <3>5. w \in DSp  BY <3>3, <3>4
    <3> QED  BY <3>5, <3>1 DEF SigS
  <2>acc. SigS(DSp) \subseteq Acceptors
    <3> SUFFICES ASSUME NEW aa \in SigS(DSp) PROVE aa \in Acceptors  OBVIOUS
    <3>1. PICK ww \in DSp : aa = Sig(ww)  BY DEF SigS
    <3>2. HasDepth(alpha, ww, MaxDepth(alpha))  BY <3>1
    <3> QED  BY <3>1, <3>2 DEF HasDepth
  <2>fin. IsFiniteSet(SigS(DSp))  BY <2>acc, <1>fa, FS_Subset
  <2>quo. SigS(DSp) \in Quorums(alpha)  BY <2>qs, <2>acc, <2>fin, QuorumUpward
  <2>dec. Decision(Msgs', alpha, b)  BY <2>quo DEF Decision, DecisionSlow
  <2> QED  BY <2>dec
<1>nec. Spec => [](W \subseteq Msgs => Decision(Msgs, alpha, b))
  BY <1>1, <1>2, PTL DEF Spec
\* --- bring in Spec, IsAll; W eventually sent, compose ---
<1> SUFFICES ASSUME Spec, IsAllMessagesEverSent(allmessages) PROVE <>Decision(Msgs, alpha, b)  OBVIOUS
<1>dia. \A m \in W : DiaMem(m)
  <2> SUFFICES ASSUME NEW m \in W PROVE DiaMem(m)  OBVIOUS
  <2>mx. m \in allmessages  BY <1>wsub
  <2>1. \A mm : (mm \in allmessages <=> IAMESCond(mm))  BY DEF IsAllMessagesEverSent
  <2> HIDE DEF IAMESCond
  <2>bic. m \in allmessages <=> IAMESCond(m)  BY <2>1
  <2>cond. IAMESCond(m)  BY <2>mx, <2>bic
  <2> QED  BY <2>cond DEF DiaMem, IAMESCond
<1>fdhyp. FD_Hyp(W)  BY <1>dia, <1>wfin DEF FD_Hyp
<1>fdgood. FD_Good(W)  BY <1>fdhyp, FiniteDiamond
<1>ev. <>(W \subseteq Msgs)  BY <1>fdgood DEF FD_Good, FD_Tgt
<1>necb. [](W \subseteq Msgs => Decision(Msgs, alpha, b))  BY <1>nec
<1> QED  BY <1>ev, <1>necb, PTL
====================================================================
