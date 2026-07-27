----------------------------- MODULE FreshDef -----------------------------
EXTENDS MessageInterface, CombinedFreshQdLrnsIdRec, TranSubMessages,
        CflId, LrnsDef

\* Fresh unfolded.  The fresh field quantifies over the strict closure
\* TranExclusive(m), identifying each recursive result with its id/lrns
\* (CflId, LrnsDef). The outer \A can stay over Tran(m) since the extra
\* x = m case is trivially satisfied by V(m) = V(m).
LEMMA FreshDef ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         NEW alpha \in Learners,
         NEW m \in Messages
  PROVE Fresh(alpha, m) = CombinedFreshQdLrnsId(m).fresh[alpha]
<1> DEFINE RR == {CombinedFreshQdLrnsId(p) : p \in TranExclusive(m)}
<1> DEFINE FF(mm) == \/ V(mm.id) = V(m)
                     \/ Con(alpha, m) \cap mm.lrns = {}
                     \/ \E pp \in RR: B(pp.id) > B(mm.id) /\ Con(alpha, m) \cap pp.lrns # {}
<1> DEFINE GG(q) == \/ V(q) = V(m)
                    \/ Con(alpha, m) \cap Lrns(q) = {}
                    \/ \E p \in TranExclusive(m): B(p) > B(q) /\ Con(alpha, m) \cap Lrns(p) # {}
<1>rec. CombinedFreshQdLrnsId(m) = CombinedFreshQdLrnsIdR(m, RR)  BY CombinedFreshQdLrnsIdRec
<1>raw. CombinedFreshQdLrnsId(m).fresh[alpha] = (\A mm \in RR : FF(mm))
  BY <1>rec DEF CombinedFreshQdLrnsIdR
<1>id. \A q \in TranExclusive(m) : /\ CombinedFreshQdLrnsId(q).id = q
                                  /\ CombinedFreshQdLrnsId(q).lrns = Lrns(q)
  <2> SUFFICES ASSUME NEW q \in TranExclusive(m) PROVE /\ CombinedFreshQdLrnsId(q).id = q
                                                      /\ CombinedFreshQdLrnsId(q).lrns = Lrns(q)  OBVIOUS
  <2>1. q \in Messages  BY TranSubMessages DEF TranExclusive
  <2>2. CombinedFreshQdLrnsId(q).id = q  BY <2>1, CflId
  <2>3. CombinedFreshQdLrnsId(q).lrns = Lrns(q)  BY <2>1, LrnsDef
  <2> QED BY <2>2, <2>3
<1>ex. \A q \in TranExclusive(m) :
          (\E pp \in RR: B(pp.id) > B(q) /\ Con(alpha, m) \cap pp.lrns # {})
          <=> (\E p \in TranExclusive(m): B(p) > B(q) /\ Con(alpha, m) \cap Lrns(p) # {})
  <2> SUFFICES ASSUME NEW q \in TranExclusive(m) PROVE
          (\E pp \in RR: B(pp.id) > B(q) /\ Con(alpha, m) \cap pp.lrns # {})
          <=> (\E p \in TranExclusive(m): B(p) > B(q) /\ Con(alpha, m) \cap Lrns(p) # {})  OBVIOUS
  <2>1. ASSUME NEW pp \in RR, B(pp.id) > B(q), Con(alpha, m) \cap pp.lrns # {}
        PROVE \E p \in TranExclusive(m): B(p) > B(q) /\ Con(alpha, m) \cap Lrns(p) # {}
    <3>1. PICK p \in TranExclusive(m) : pp = CombinedFreshQdLrnsId(p)  BY <2>1
    <3>2. pp.id = p /\ pp.lrns = Lrns(p)  BY <3>1, <1>id
    <3> QED BY <2>1, <3>2
  <2>2. ASSUME NEW p \in TranExclusive(m), B(p) > B(q), Con(alpha, m) \cap Lrns(p) # {}
        PROVE \E pp \in RR: B(pp.id) > B(q) /\ Con(alpha, m) \cap pp.lrns # {}
    <3>1. CombinedFreshQdLrnsId(p) \in RR  BY <2>2
    <3>2. CombinedFreshQdLrnsId(p).id = p /\ CombinedFreshQdLrnsId(p).lrns = Lrns(p)  BY <2>2, <1>id
    <3> QED BY <2>2, <3>1, <3>2
  <2> QED BY <2>1, <2>2
<1>gg. \A q \in TranExclusive(m) : FF(CombinedFreshQdLrnsId(q)) <=> GG(q)
  <2> SUFFICES ASSUME NEW q \in TranExclusive(m) PROVE FF(CombinedFreshQdLrnsId(q)) <=> GG(q)  OBVIOUS
  <2>1. CombinedFreshQdLrnsId(q).id = q /\ CombinedFreshQdLrnsId(q).lrns = Lrns(q)  BY <1>id
  <2>2. (\E pp \in RR: B(pp.id) > B(CombinedFreshQdLrnsId(q).id) /\ Con(alpha, m) \cap pp.lrns # {})
        <=> (\E p \in TranExclusive(m): B(p) > B(q) /\ Con(alpha, m) \cap Lrns(p) # {})
    BY <1>ex, <2>1
  <2> QED BY <2>1, <2>2
<1>2. (\A mm \in RR : FF(mm)) <=> (\A q \in TranExclusive(m) : GG(q))
  <2>1. ASSUME \A mm \in RR : FF(mm), NEW q \in TranExclusive(m) PROVE GG(q)
    <3>1. CombinedFreshQdLrnsId(q) \in RR  OBVIOUS
    <3> QED BY <2>1, <3>1, <1>gg
  <2>2. ASSUME \A q \in TranExclusive(m) : GG(q), NEW mm \in RR PROVE FF(mm)
    <3>1. PICK q \in TranExclusive(m) : mm = CombinedFreshQdLrnsId(q)  BY <2>2
    <3> QED BY <2>2, <3>1, <1>gg
  <2> QED BY <2>1, <2>2
<1>m. m \in Tran(m)  BY DEF Tran
<1>raw2. CombinedFreshQdLrnsId(m).fresh[alpha] = (\A q \in TranExclusive(m) : GG(q))  BY <1>raw, <1>2
<1>4. (\A x \in Tran(m) : GG(x)) <=> (\A q \in TranExclusive(m) : GG(q))
  <2>1. Tran(m) = TranExclusive(m) \cup {m}  BY <1>m DEF TranExclusive
  <2>2. GG(m)  OBVIOUS
  <2> QED BY <2>1, <2>2
<1>fresh. Fresh(alpha, m) = (\A x \in Tran(m) : GG(x))  BY DEF Fresh
<1> QED BY <1>raw2, <1>4, <1>fresh
====================================================================
