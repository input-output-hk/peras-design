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

We spend the first half of the morning discussing the agenda for the workshop and the goals of the Peras innovation stream:
* What things can be handed-over?
* What things need to be polished, worked on more, before we can publish or hand them over?
* What's our roadmap for the second half of the year?

We also discuss the state of ΔQ framework and possible improvements:
* what's the current state of libraries?
* what are options/ideas for improving those libraries and make this methodology more widely accessible and useful?
* what are PNSoL plans? what are opportunities collaboration?

## State of the Protocol

We then spent time delving into the details of the current state of the protocol, ensuring alignment between innovation and research.

A first question was: when is publication planned? what's the state of research?
  * we know how to do it :tada:, where `it` means proving the main properties of the protocol, eg. the expected settlement time
  * there's a need for more details for the rest of the "thing", so it's more about doing the required "leg work" than deep thinking at this stage
  * a rough target would be to be ready for submission around 09/2024

The main issue preventing opening the protocol publicly was that
people would be "scooping" the protocol but given the intricacy of the
proofs, that's quite unlikely at this stage.

Some more detailed questions ensue:

* [x] What to do about _pre-agreement_?
  * Having a v1 w/o pre-agreement is just fine
  * pre-agreement is orthogonal to the main protocol, it can be implemented later
  * v1 will not _guarantee_ fast-settlement, but should work in practice given what we know of the behaviour of the network
  * importantly, pre-agreement protects against cooldown within the 25% adversarial stake margin
* [x] do we need to check certificate time is lower than Delta?
  * it's definitely needed for the (paper) proof
  * the key insight is that it manipulates 2 strings, 1 slot leadership string, 1 voting string, and this defines a graph compatible with the axioms of the protocol (eg. Δ delivery bound, adversarial stake...)
  * it's easier to have  certainty about delivery of the certificates?
  * _but_ it adds more code to the implementation as it needs to keep track of votes/certificates delivery time
  * this is mostly problematic for Agda spec & Conformance test, but we could still inject votes/certs at different point in time?
  * _conclusion_: let's keep it for now!
* [x] committee size and other parameters range/constraints (see [tech-report #2](https://github.com/input-output-hk/peras-design/blob/main/site/reports/tech-report-2.md#constraints-on-peras-parameters))
  * we go through all parameters and their mentioned constraints
  * need to remove L <= U constraint and some other adjustments
* [x] is τ is a function of _mean_ committee size?
  * yes, fluctuation in actual committee size are smaller when size grows but they are expected
* [x] we review adversarial analytics
  * underlying question is: how to provide a framework for estimating the parameters?
  * this raises the interesting question of simulating and/or visualising the private chain attack? how much would it cost?
  * as we discuss _how_ a private chain attack could be carried over,
    someone mentions https://nodemesh.cc/ which provide a service for
    faster inclusion of tx on-chain by ensuring tx are submitted
    "close" to SPOs' block producers
* [x] We discuss the current state of [votes & certificates analysis](https://github.com/input-output-hk/peras-design/blob/f4a5646a6c043738d15957eb8096e22e4f959469/peras-vote/src/Peras/Voting/Vote.hs#L17)
  * Makes sense overall
  * Anatolyi Zinovyev will start an internship, can work on definitive voting scheme for Peras and Leios?

## Research/Engineering Collaboration

We covered two main topics here: When/how to publish Peras' R&D stream results (website and github repository), and how to improve collaboration between research and innovation?

On the publication of our results: We need to get the objectives clear but of course stating we are not solving all the problems. What's important to highlight for Peras:
  * it provides fast-settlement
  * it handles fluctuating participation
  * it's self-healing & can recover from failures

On the overall collaboration process, major next step is Leios. We need to collaborate with Spyros on the network simulations as they are critical for publication in top-tier venues.

# Day 2

## Implementation

We discussed some questions related to practical implementation of Peras, as we want to ensure we provide sound and useful advices to future implementors of the protocol.

The main discussion revolves around votes and certificates storage which will be the most impactful in terms of implementation:
* Do you need votes if you have certs?
  * _no_
* Which certs do you need?
  * see block creation rules 1.2.a: it requires we are able to check certificates up to 2 rounds in the past, and of course requires inclusion of latest `cert'`
* What and where to store things (votes and certificates)?
  * _This should be left implementation dependent_
* Can we prove that if you forget the certificates more than X slots in the past, you are safe?
* :warning: The chain cannot be the only canonical source of truth anymore as nodes need to be able to provide certificates to prove their chain is the heaviest
* We need to _specify_ the transport layer for votes and certificates, in particular the CDDL schemas and protocol details in order to ensure interoperability
  * how to retrieve historical votes
* What would a specific protocol for vote synchronisation look like?
  * Could it be something like pub/sub? _this does not seem appropriate_
  * There's a custom mini-protocol being worked on as part of mithril/cardano integration -> https://hackmd.io/yn9643iKTVezLbiVb-BzJA?view#Message-Submission-mini-protocol
* change to the block body is minimal: we only need recording of cert*, but there may be various options to do so:
  * store full cert in the block => seems safer, does not need to wait for certificate to accept block, happens rarely anyway
  * store hash of it -> have the certificate elsewhere
  * not store it
* do we need to store votes & certs forever?
  * yes for certs, votes can be considered transient and discarded after a while (when?)
* can we put certificates on-chain?
  * _probably not_
* deferring certificate/vote check to avoid having certificates download on critical path?
  * do we still have the problem that we need certs/votes to choose select best chain?
  * that's not a problem because votes and certs are diffused separately
  * the chain selection rule have to be adapted to handle incoming new
    certificates, but we don't risk anymore flip-flop problems with an
    adversary releasing votes strategically to force us to switch
    chain on every vote

## Planning

### Q2 Goals

* Reviewing the Q2 goals:
  * 1 done  [INN-90](https://input-output.atlassian.net/browse/INN-90)
  * 1 nearly completed (tech report -> CIP draft) [INN-89](https://input-output.atlassian.net/browse/INN-89)
  * 1 started but not completed (conformance suite) [INN-91](https://input-output.atlassian.net/browse/INN-91)
* Short term actions pursuant to completing Q2
  * complete tech report
  * ask RW & MB about proper CIP format/expectations
  * draft a CIP pulling stuff from TR#2
  * make website and repo public

### What's next?

What do we want to do next?

* **note**: AB on "sabbatical" for 2 months starting the week of 22/07
* Need more work on conformance suite (Agda <-> Haskell)
  * organise a workshop with Santiago/Chris/Nick/Damian/Pi on "good conformance suite" and "specification"?
  * brand it as Intersect Consensus Technical WG
  * external feedback on conformance test (node/protocol) value -> depends on who you ask?
* moving from "pre-alpha" to "alpha" version requires paper to be published
* what about parameters value? recommendations?
  * work with _partner chains_ to get some requirements
  * we should provide guidelines but need actual calculations to be done "in the field"
  * users should have a tool to be able to calculate themselves the needed parameters
  * work with Peter Gazi on tooling/computations
* improve existing chain simulator
  * some scenarios we can work on: split brain, larger networks, longer simulations
  * what could be useful for paper publication = concrete numbers on private chain attack, how many rounds you have to wait for settlement (negligible probability of fork)?
* improve network simulator, eg. make [PeerNet](https://github.com/PeerNet/PeerNet) more widely usable
  * we could work on the basis of [ce-netsim]() and enhance it to match PeerNet's features
  * it's useful and needed for Leios too
  * :warning: acceptance of a generic tool might be hard to get and it easily could become shelfware
* make ΔQ more usable
  * provide out-of-the-box and possibly interactive visualisation
  * provide faster numeric computations (eg. using discretised CDFs and fast vector operations, possibly offloaded to GPU)
* we might shift focus on Leios which is only getting started
* for Q3 planning, we want to provide _options_ and get decision from stakeholders
  * polish what we have
  * no more polish and switch on something else
  * tools & frameworks
* complete voting string proof (and others?)
  * for publication, it would be useful to have the "full monty" but would change the shape of the paper, as it focuses on the formalisation part
  * a less ambitious but more realistic goal would be to consider the formal spec work for Peras as a _PoC_ that we can connect Research <-> FM <-> Test
  * Work on Praos specification has started, more bottom up approach, could be a good follow-up to reuse the techniques and tools we experimented here

## Markov chain simulations

BB walks us through his work on [Markov chain](https://github.com/input-output-hk/peras-design/blob/f4a5646a6c043738d15957eb8096e22e4f959469/peras-markov/ReadMe.md#L1) simulations

* Basic principle: represents the whole network with an Adversary _coordinating_, and approximate all honest nodes as a _single node_
* at each slot, the network has 4 possible transitions each with an attached probability:
  1. no blocks
  2. honest block
  3. adversary block
  4. both blocks
* similarly at each round, there are 4 transitions:
  1. no quorum
  2. honest quorum
  3. adversarial quorun
  4. mixed quorum
* state is very small, just a few numbers to keep around
* private chain attack classical paper https://arxiv.org/pdf/1311.0243

Benefits:
* Can take into account small probabilities which detailed simulation are blind to
* we can later on connnect to Agda specification by assigning probabilities to the transition relations
* we can define QC generators based on those probabilities

* looking at Ouroboros paper for application?
  * https://eprint.iacr.org/2016/889.pdf  p.27
* model reach/margin random walk for Peras using MC -> compute joint distribution of μ and ρ
  * expected waiting time?

* compute the dynamics of μ and ρ analytically (symbolic)

## Conformance testing

We review current code from [Quviq](https://github.com/input-output-hk/peras-design/pull/144) with an aim to replace voting rules with the ones from the specification

* The `Dec xx` functions need to be Agda2hs compatible => need to rewrite most of them
* The TC has some troubles inferring types from the decidable functions, possibly because of renamings (?)
* We need to work on a Haskell-side blocktree implementation, which might be problematic because of the dependencies on stdlib (implement `toTree`)
  * might need to use MAlonzo, which we'll try to avoid
* Remove Haskell code from Agda code -> see if we need it, or can pull it from Agda formal spec, or move it to proper Haskell

We would like to have just a `record` on the Agda side describing the state machine, and call the right functions from the Haskell side

::: note

This attempt sort of contradicts the approach proposed by Quviq which rests on:

* A test model in Agda that can "easily" be projected to Haskell
* Soundness proof that relates the test model to the formal model

In this case, we don't need `Dec`idable versions of the functions used
by the formal spec, or we can make them part of the test model and
prove they are sound w.r.t. the formal model. This has the benefits of
simplifying the projection to Haskell and insulate it from Agda's
`stdlib` percolating.

:::
