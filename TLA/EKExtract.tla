------------------------------ MODULE EKExtract ------------------------------
EXTENDS HPaxosPlusCal
LOCAL INSTANCE TLAPS

\* Extract EventuallyKnownInvariant's leads-to at a specific mm: EventuallyKnown-
\* Invariant's \A ranges over a temporal (~>) body, so instantiate via the
\* []-Barcan-equality + opaque wrapper (EKBoxOp) route (skill wall #7). Bound
\* variable m matches EventuallyKnownInvariant's own (no []-alpha-rename).
LEMMA EKExtract ==
  ASSUME []EventuallyKnownInvariant, NEW mm \in SUBSET Messages
  PROVE  EKLT(mm)
<1>1. [](\A m \in SUBSET Messages : EKLT(m))
  <2>1. []EventuallyKnownInvariant  OBVIOUS
  <2> QED  BY <2>1, PTL DEF EventuallyKnownInvariant, EKLT
<1>bar. (\A m \in SUBSET Messages : [](EKLT(m))) <=> ([](\A m \in SUBSET Messages : EKLT(m)))
  OBVIOUS
<1>all. \A m \in SUBSET Messages : EKBoxOp(m)  BY <1>1, <1>bar DEF EKBoxOp
<1> HIDE DEF EKBoxOp
<1>m. EKBoxOp(mm)  BY <1>all
<1> QED  BY <1>m, PTL DEF EKBoxOp
====================================================================
