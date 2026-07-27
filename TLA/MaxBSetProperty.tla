------------------------- MODULE MaxBSetProperty -------------------------
\*   FiniteMaxExists -> cited lemma (and, through it, FiniteSetTheorems)
EXTENDS MessageInterface, FiniteMaxExists

\* Max({ProposalBal(x) : x \in T}), for any finite nonempty T \subseteq Proposals,
\* is itself a member of that set and an upper bound for it.
LEMMA MaxBSetProperty ==
    ASSUME TypeOKMessageInterface,
           NEW T, IsFiniteSet(T), T # {}, T \subseteq Proposals
    PROVE /\ Max({ProposalBal(x) : x \in T}) \in {ProposalBal(x) : x \in T}
          /\ \A y \in {ProposalBal(x) : x \in T} : Max({ProposalBal(x) : x \in T}) >= y
<1>bal. \A x \in T : ProposalBal(x) \in Nat
  <2>1. ASSUME NEW x \in T PROVE ProposalBal(x) \in Nat
    <3>1. MessageInterface.proposalbal \in [Proposals -> Ballots]
      BY DEF TypeOKMessageInterface
    <3> QED BY <2>1, <3>1 DEF ProposalBal, Ballots
  <2> QED BY <2>1
<1>max. \E r \in T : \A y \in T : ProposalBal(y) <= ProposalBal(r)
  BY <1>bal, FiniteMaxExists
<1>r. PICK r \in T : \A y \in T : ProposalBal(y) <= ProposalBal(r)  BY <1>max
<1>rInT. ProposalBal(r) \in {ProposalBal(x) : x \in T}  BY <1>r
<1>rUB. \A y \in {ProposalBal(x) : x \in T} : y <= ProposalBal(r)
  <2>1. ASSUME NEW y \in {ProposalBal(x) : x \in T} PROVE y <= ProposalBal(r)
    <3>1. PICK x \in T : y = ProposalBal(x)  BY <2>1
    <3> QED BY <3>1, <1>r
  <2> QED BY <2>1
<1>witness. \E x \in {ProposalBal(z) : z \in T} : \A y \in {ProposalBal(z) : z \in T} : x >= y
  BY <1>rInT, <1>rUB
<1> QED BY <1>witness DEF Max
====================================================================
