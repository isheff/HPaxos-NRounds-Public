# HPaxos-NRounds-TLA
TLAPS formalization of NRound HPaxos, with proofs, refactored with 2026-07 definitions.

## Refactor
I attempted to simplify some things. 
For example, instead of having a predicate `B(ballot, message)`, we have a function `B(message)` that returns a ballot (and we prove that it is a total function). 
Instead of using `WellFormed` everywhere, we have a set of `Messages` defined so that they are all `WellFormed`, and those are the only things allowed on the network. 
The definitions of `Refs` and `Prev` are now a little different, but they're not too weird. 

I now use small modules: each lemma and theorem is its own module. 
This makes `tlapm` proof checking _much_ faster: just run a bash loop or whatever to check `tlapm` over every `*.tla`. 

### `depgraph.py`
Because it's annoying to follow proofs when they're all split up like this, I added a python script that makes a dependency graph (as an svg) of a given module name. 
For example, try `./depgraph.py AgreementM`, and it will make an svg that is hopefully useful in following how the `AgreementM` proof works. 


## Organization
The idea here is that rather than building a concrete set of Messages and stuff, I establish ``Interfaces,'' sets of assumptions about constant sets of Messages, Values, Learners, etc. 
All the proofs that follow are then based only on those assumptions. 
The proofs cannot use unexpected quirks of specific constructions: there are none in scope. 
For each Interface, there are specific constructions (in separate files) proven to meet the assumptions.

This culminates in `HPaxosPlusCal`, a very simple PlusCal protocol that implements HPaxos. 
`SafeAcceptors` simply receive messages (for which they already know the transitive histories), and send a message if they can. 
Everyone else (including proposers) sends any message (not signed by anyone in `SafeAcceptors`), so long as the transitive history is already sent (we're modeling the fact that no one receives a message if its transitive history isn't sent anyway). 

Termination then assumes that if you can send a ``correct final proposal'' (which technically requires knowing all the messages below some ballot that will ever be on the network, something that can only be implemented with at least partial synchrony), you eventually get a decision. 

## LearnerGraphInterface
Sets out the assumptions about learner graphs.
See `LearnerGraphConcrete` for a real, heterogeneous learner graph and `LearnerGraphConcreteSupportsAssumptions` for proof that it supports those assumptions. 

## ValueInterface
Sets out assumptions about values and their relationship to ballots (including `BalToVal`).
See `ValueConcrete` for an instantiation of (any subset of) `Nat`s as Values, supporting those assumptions, and `ValueConcreteSupportsAssumptions` for proof that it does indeed support those assumptions.


## MessageInterface
Sets out assumptions about (well-formed) messages that the protocol can use. 
This then defines a bunch of useful macros, like `IsTwoA` and such. 
Note that if you're going to prove stuff about macro `HasDepth`, you want to use lemma `HasDepthDef`, since its actual definition is defined in a complicated way in order to support recursion. 

### Some very important lemmas are just about messages.
We prove, for example, `AgreementM`, that for any set of Messages satisfying all these assumptions, any two contradictory decisions prove their learners are disconnected. 
We also prove `MultiplePrevImpliesCaught`, which says that any message with multiple `Prev`s catches its signer, and `CaughtPrev`, which proves that the definition of `Caught` we're using (two messages in the transitive history, neither of which is in the transitive history of the other) is exactly equal to the other definition of Caught (two messages in the transitive history that share a `Prev`).

### `MessageConcrete` and `HPaxosPlusCalConcrete`
See `MessageConcrete` for a real construction of the set of messages, and `MessageConcreteSupportsAssumptions` for proof that it supports these assumptions.

In `HPaxosPlusCalConcrete`, we specify exactly what `HPaxosPlusCal` looks like when you use the concrete Messages instantiation. 
Safe Acceptors track a set of `recent_messages`, and use that to construct and sent messages. 
In `HPaxosPlusCalConcreteSpecEquivalence`, we prove that this is exactly equivalent to `HPaxosPlusCal` (when using the concrete instantiation of `MessageInterface`), except of course that it defines `recent_messages`, which is always strictly a function of `Msgs` and `known_messages`. 


## HPaxosPlusCal
The actual live protocol is very simple, and most of the proofs follow directly from facts proven in `MessageInterface`. 
`Termination` is the Exception: we want to prove that these simple, ``greedy'' acceptors are enough to guarantee termination (given a proposer who proposes the right thing). 

## Current Status
Key proven theorems:
- `AlwaysAgreementInvariant` : key agreement safety property.
- `TerminatingProposalRelaxed` : if you send any proposal with ``the right'' `Tran` and value, and a high enough ballot, you can make a learner decide, if you wait long enough. 
- `Termination` That proposal exists, so there is indeed a proposal you can send that will make a learner decide. 
