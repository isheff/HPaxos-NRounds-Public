----------------------- MODULE CatchWitnessCorrect -----------------------
EXTENDS MessageInterface

LEMMA CatchWitnessCorrect ==
  ASSUME TypeOKMessageInterface, NEW mm \in SUBSET Messages, NEW s,
         s \in CaughtS(TranClosure(mm))
  PROVE /\ CatchWitness1(mm,s) \in TranClosure(mm)
        /\ CatchWitness2(mm,s) \in TranClosure(mm)
        /\ Sig(CatchWitness1(mm,s)) = s /\ Sig(CatchWitness2(mm,s)) = s
        /\ CatchWitness1(mm,s) \notin Tran(CatchWitness2(mm,s))
        /\ CatchWitness2(mm,s) \notin Tran(CatchWitness1(mm,s))
<1>ex. \E x \in TranClosure(mm) : \E y \in TranClosure(mm) :
         /\ Sig(x) = s /\ Sig(y) = s
         /\ x \notin Tran(y) /\ y \notin Tran(x)
  BY DEF CaughtS
<1>c1props. /\ CatchWitness1(mm,s) \in TranClosure(mm)
            /\ \E y \in TranClosure(mm) :
                 /\ Sig(CatchWitness1(mm,s)) = s /\ Sig(y) = s
                 /\ CatchWitness1(mm,s) \notin Tran(y) /\ y \notin Tran(CatchWitness1(mm,s))
  BY <1>ex DEF CatchWitness1
<1>c2props. /\ CatchWitness2(mm,s) \in TranClosure(mm)
            /\ Sig(CatchWitness1(mm,s)) = s /\ Sig(CatchWitness2(mm,s)) = s
            /\ CatchWitness1(mm,s) \notin Tran(CatchWitness2(mm,s))
            /\ CatchWitness2(mm,s) \notin Tran(CatchWitness1(mm,s))
  BY <1>c1props DEF CatchWitness2
<1> QED BY <1>c1props, <1>c2props
====================================================================
