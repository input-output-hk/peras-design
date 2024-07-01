# Edinburgh Team Workshop

## Agenda

| Goal/Topic                                                 | Items                                                                                    | Actions                                            |
|------------------------------------------------------------|------------------------------------------------------------------------------------------|----------------------------------------------------|
| **Define/improve available public stuff on Peras**         | currently, https://peras.cardano-scaling.org contains minimal content,                   | Fleshout website                                   |
|                                                            | how much of https://github.com/input-output-hk/peras-design can we add there?            | Polish code repo                                   |
|                                                            |                                                                                          | Review material                                    |
|                                                            |                                                                                          | Go public                                          |
| **Action items and next steps**                            | high-priority items for this PI                                                          | Finalise technical report #2                       |
|                                                            | At least make sure we have a ToC covering all we wanted to cover                         |                                                    |
| **Reflect & plan on improving Research/Eng collaboration** | proof techniques                                                                         | focus on network simulation work for Leios         |
|                                                            | Custom DSL                                                                               |                                                    |
|                                                            | https://github.com/EasyCrypt/easycrypt                                                   |                                                    |
|                                                            | research focused development environment and tools                                       |                                                    |
|                                                            | what kind of specs do we want?                                                           |                                                    |
| **Internship contribution to Innovation Streams?**         |                                                                                          | Anatolyi to talk to Arnaud                         |
|                                                            |                                                                                          | Work on ALBA at start then SNARKs                  |
| **protocol**                                               | what to do about preagreement?                                                           |                                                    |
|                                                            | do we need certificate time < Delta check?                                               |                                                    |
|                                                            | committee size and other parameters range/constraints ?                                  | Clean-up parameters table in tech report           |
| **votes and certificates**                                 | review proposed Vote structure & process                                                 | Detail comparison of approaches in the tech report |
|                                                            | review ALBA construction                                                                 | Work with crypto engineers to validate approach    |
|                                                            | benchmarks & caveats                                                                     |                                                    |
|                                                            | diffusion delta-Q model                                                                  |                                                    |
| **implementation concerns**                                | do we need to store votes & certs forever?                                               |                                                    |
|                                                            | can we put certificates on-chain?                                                        |                                                    |
|                                                            | deferring certificate/vote check to avoid having certificates download on critical path? |                                                    |
|                                                            | we still have the problem that we need certs/votes to choose select best chain           |                                                    |
| **adversarial scenarios and analyses**                     | is current list of adversarial scenarios complete?                                       | Review analyses from research side                 |
|                                                            | review process for analyses?                                                             |                                                    |
| **conformance tests**                                      | review Quviq's model and link to Agda specification                                      |                                                    |
|                                                            | align research/spec/test/reference implementation                                        |                                                    |
|                                                            | remaining work on conformance model                                                      |                                                    |
|                                                            | work on adversarial model-based testing                                                  |                                                    |
|                                                            | list properties of interest                                                              |                                                    |
| **Markov chain simulation for adversarial**                | what kind of behaviour can we simulate?                                                  |                                                    |
|                                                            | how can we extend the framework?                                                         |                                                    |

# Day 1

## Agenda/Planning

* What things can be  handed-over?
* What things need to be polished, worked on more, before we can publish or hand them over?
* We need to define some kind of roadmap for next steps (CIP? RFP?)
* Discussion about the state of ΔQ:
  * current state of libraries
  * options/ideas
  * PNSoL plans? collaboration?

## State of the Protocol

* Q: when is publication planned? what's the state of research?
  * we know how to do it :tada:
  * how to prove expected settlement?
  * more details for the rest of the thing
  * -> 09/2024 ?
* main issue preventing publication is people scooping the protocol but given the intricacy of the proofs, that's quite unlikely at this stage

* [x] What to do about pre-agreement?
  * v1 w/o pre-agreement is just fine
  * pre-agreement is orthogonal, can be implemented later
  * v1 does not _guarantee_ fast-settlement in theory, but should work in practice
  * pre-agreement protects against cooldown with < 25% adversarial stake
* [x] do we need certificate time < Delta check?
  * needed for the (paper) proof
  * 2 strings = 1 slot leadership string, 1 voting string
  * this defines a compatible graph (=> axioms)
  * easier to have the certainty about delivery of the certificates?
  * adds more code to the implementation (need to keep track of votes/certificates delivery time)
  * problematic for Agda spec & Conformance test (could still inject votes/certs at different point in time?)
  * let's keep it for now!
* [x] committee size and other parameters range/constraints (see [tech-report #2](https://github.com/input-output-hk/peras-design/blob/main/site/reports/tech-report-2.md#constraints-on-peras-parameters))
  * remove L <= U constraint
  * Check simulation?
* [x] τ is a function of _mean_ committee size
  * fluctuation in actual committee size are smaller when size grows
* [x] adversarial analytics
  * how to provide a framework for estimating the parameters?
  * simulating/visualising the private chain attack? how much would it cost?
  * briefly mention https://nodemesh.cc/ which provide a service for faster inclusion of tx on-chain by ensuring tx are submitted "close" to SPOs' block producers
* [ ] Votes & certificates
  * Makes sense overall
  * Anatolyi Zinovyev will start an internship, can work on definitive voting scheme for Peras and Leios
* ambiguities of the protocol?

## Research/Engineering Collaboration

* Getting the objectives clear but not stating we are solving all the problems
  * fast-settlement
  * fluctuating participation
  * self-healing & recovery from failures

* Leios
  * network simulations => work w/ Spyros
  * critical for publication of the Leios in top-tier venues

# Day 2

## Implementation

* Do you need votes if you have certs? => no
* Which certs do you need?
  * on-line -> see block creation rules 1.2.a
* What and where to store things?
* Can we prove that: if you forget the certificates more than X slots in the past, you are safe?
* Option 1:
  * 2 types of certificates stored ?
* :warning: The chain cannot be the only canonical source of truth anymore
* specify transport layer for votes
  * how to retrieve historical votes
* specific protocol for vote synchronisation -> pub/sub?
  * custom mini-protocol being worked on as part of mithril/cardano integration -> https://hackmd.io/yn9643iKTVezLbiVb-BzJA?view#Message-Submission-mini-protocol
* minimal change to the body -> recording of cert*, various options
  * store full cert in the block => seems safer? does not need to wait for certificate to accept block, happens rarely anyway
  * store hash of it -> have the certificate elsewhere
  * not store it
* do we need to store votes & certs forever?
  * yes for certs, votes can be considered transient and discarded after a while (when?)
* can we put certificates on-chain?
  * probably not
* deferring certificate/vote check to avoid having certificates download on critical path?
  * do we still have the problem that we need certs/votes to choose select best chain?
  * yes, but that's not a problem because votes and certs are diffused separately
* certs must be stored independently

## PI Planning

* PI6 goals:
  * 1 done
  * 1 nearly completed (tech report -> CIP draft)
  * 1 started but not completed (conformance suite)
* Next steps for PI6
  * complete tech report
  * ask RW & MB about proper CIP format/expectations
  * draft a CIP pulling stuff from TR#2
  * make website and repo public

* What do we want to do next?
  * **note**: AB on "sabbatical" for 2 months starting the week of 22/07
  * work on conformance suite (Agda <-> Haskell)
    * organise a workshop with Santiago/Chris/Nick/Damian/Pi on "good conformance suite" and "specification"?
    * brand it as Intersect Consensus Technical WG
    * external feedback on conformance test (node/protocol) value -> depends on who you ask?
  * pre-alpha -> alpha ? requires paper done
  * parameters value? recommendations?
    * work with partner chains to get some requirements
    * we should provide guidelines but need actual calculations
    * give "users" tool to calculate them?
    * work with Peter Gazi on tooling/computations
  * improve simulator -> split brain, larger networks, longer simulations
    * useful for paper = concrete numbers on private chain attack, how many rounds you have to wait for settlement (negligible probability of fork)?
  * network simulator (Spyros' stuff but more usable?)
    * enhance ce-netsim?
    * useful for Leios too
    * acceptance of a generic tool might be hard to get (=> shelfware)
  * make ΔQ more usable
    * interactive visualisation
    * fast numeric computations
  * focus on Leios?
  * PI7 => options?
    * polish what we have
    * no more polish
  * complete voting string proof (and others?)
    * for publication, it would be useful to have the "full monty" but would change the shape of the paper, focusing on the form alisation part
    * more a PoC that we can connect Research <-> FM <-> Test
    * Work on Praos specification has started, more bottom up approach, could be a good follow-up to reuse the techniques and tools we experimented here

## Markov chain simulations

* Adversary coordinating, approximate honest nodes as a single node
* at each slot, 4 options
  1. no blocks
  2. honest block
  3. adversary block
  4. both blocks
* similarly at each round
  1. no quorum
  2. honest quorum
  3. adversarial quorun
  4. mixed quorum
* state is very small, just a few numbers to keep around
* private chain attack classical paper https://arxiv.org/pdf/1311.0243


Benefits:
* Can take into account small probabilities which detailed simulation are blind to
* connnect to Agda specification by assigning probabilities to the transition relations
* QC generators based on those probabilities

* looking at Ouroboros paper for application?
  * https://eprint.iacr.org/2016/889.pdf  p.27
* model reach/margin random walk for Peras using MC -> compute joint distribution of μ and ρ
  * expected waiting time?

* compute the dynamics of μ and ρ analytically (symbolic)

## Conformance testing

* Looking at current code from [Quviq](https://github.com/input-output-hk/peras-design/pull/144) to replace voting rules with the ones from the specification
* The `Dec xx` functions need to be Agda2hs compatible => need to rewrite most of them
* The TC has some troubles inferring types from the decidable functions, possibly because of renamings (?)
* We need to work on a Haskell-side blocktree implementation, which might be problematic because of the dependencies on stdlib (implement `toTree`)
  * might need to use MAlonzo, which we'll try to avoid
* Remove Haskell code from Agda code -> see if we need it, or can pull it from Agda formal spec, or move it to proper Haskell

We would like to have just a `record` on the Agda side describing the state machine, and call the right functions from the Haskell side
