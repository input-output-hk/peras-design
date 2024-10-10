---
title: "A project's retrospetive"
---

On the 2nd of October, the Peras team spent some time reflecting on the project and wrote some "post-mortem" thoughts that seem worthwhile to be shared.
This post is a summary of these discussions along with a short timeline and possible next steps.

## Project's Timeline

| Date       | Event                                                                                                                                                                                                                                                                   |
|------------|-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 2023-09-29 | Engineering/Research Peras workshop in Edinburgh - [First commits](https://github.com/input-output-hk/peras-design/commit/85e8e124c79768eb24549c39de88433545be1c6d) to Peras repository - Revised version of algorithm version                                          |
| 2023-11-20 | First video update on Peras project - Draft project's charter and form team                                                                                                                                                                                             |
| 2024-02-05 | Started work on [simulation](https://github.com/input-output-hk/peras-design/commit/2bc084ae078ef22ffef8a91cb67c94e31576f20c) - Started work on [Agda](https://github.com/input-output-hk/peras-design/commit/d90f164d5b5d1ac15bc6c8126d8180addb872681) Haskell & model |
| 2024-04-09 | First Team workshop in Paris -  "Final" version of algorithm (aka. pre-alpha) for deployment                                                                                                                                                                            |
| 2024-04-15 | [First version](https://github.com/input-output-hk/peras-design/commit/c85bec9c27a2e5dd7c821304a65c3eabd327f752) of quickcheck-dynamic and Agda workflow                                                                                                                |
| 2024-04-18 | [Technical Report #1](https://github.com/input-output-hk/peras-design/commit/997c0be361f22273bbea5b4e445dd9bdf0850183) reviewed                                                                                                                                         |
| 2024-06-26 | Team workshop in Edinburgh -  CIP draft started                                                                                                                                                                                                                         |
| 2024-07-10 | Relation specification completed - Soundness proofs started                                                                                                                                                                                                             |
| 2024-07-15 | [Technical Report #2](https://github.com/input-output-hk/peras-design/commit/50a9354695343f5eaebc899ec7da457a00c5a24f)                                                                                                                                                  |
| 2024-08-01 | [Website published](https://github.com/input-output-hk/peras-design/commit/0c0d797f7e2bac16a8e247724e1ed7cffe2c151c)                                                                                                                                                    |
| 2024-08-14 | [CIP](https://github.com/cardano-scaling/CIPs/commit/5942b8f49a4e21f43c0905512cb18f3735aed93e) completed, sent for internal review                                                                                                                                      |
| 2024-09-27 | Conformance tests finalized.                                                                                                                                                                                                                                            |
| 2024-10-02 | [Last Monthly demo](https://docs.google.com/presentation/d/1CIEOJrXorzsQagE1zi7S9VFts7AT1inEuC332JmNsjM/edit?usp=sharing)                                                                                                                                               |
| 2024-10-21 | IO R&D seminar                                                                                                                                                                                                                                                          |

## Project Outcomes

How does the team assess achievement of stated primary and secondary goals (see Modelling Ouroboros Peras document), and production of expected deliverables.

### Primary Goals

| Goal                                           | Achieved? | Comment                                                                                                       |
|------------------------------------------------|-----------|---------------------------------------------------------------------------------------------------------------|
| Expected impact on transaction settlement time | 🟢        | See [Technical report](/docs/reports/tech-report-2)                                                           |
| Operational and performance profile            | 🟢        | See [Technical report](https://peras.cardano-scaling.org/docs/reports/tech-report-2#settlement-probabilities) |
| Design and architecture of potential solution  | 🟡        | We did not want to overly restrict implementors but CIP provides a detailed specification                     |

### Secondary Goals

| Goal | Achieved? | Comment |
|------|-----------|---------|
| Use the models as formal foundation for publications |  🔴 | Remains to be seen, some discussions in progress, but awaiting |
| Demonstrate use of FM as communication tool between Research and Engineering |  🟡 | Was done informally, need more work |
| Build reusable tools, libraries, and methods | 🟡| Some contributions in progress (q-d, ce-netsim, deltaQ)|

### Deliverables

| Deliverable                                                                | Completed?                                                                                                                                                                            |
|----------------------------------------------------------------------------|---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| An executable formal model of the Ouroboros Peras protocol                 | 🟢 [code](https://github.com/input-output-hk/peras-design/blob/main/src/Peras/Conformance/Model.agda)                                                                                 |
| A prototype of Peras protocol components                                   | 🟢 [code](https://github.com/input-output-hk/peras-design/blob/main/peras-simulation/src/Peras/Prototype/Node.hs)                                                                     |
| A tool and a method to validate any implementation                         | 🟢 [code](https://github.com/input-output-hk/peras-design/blob/main/peras-simulation/src/Peras/Conformance/Test/External.hs)                                                          |
| A simulation of a network of nodes implementing Peras + simulation results | 🟢 [code](https://github.com/input-output-hk/peras-design/blob/main/peras-server/src/Peras/Server.hs) [code ](https://github.com/input-output-hk/peras-design/tree/main/peras-markov) |
| Appropriate documentation                                                  | 🟢 [site](https://peras.cardano-scaling.org)                                                                                                                                          |
| A journal of the whole development process                                 | 🟢 [logbook](https://github.com/input-output-hk/peras-design/blob/main/Logbook.md)                                                                                                    |
| Evaluation of the deliverable with respect to the aforementioned goals     | 🟢 [reports](https://peras.cardano-scaling.org/docs/reports/) [cip](https://github.com/cardano-scaling/CIPs/blob/bwbush/peras/CIP-0PRS/README.lagda.md)                               |


## Final Retrospective Outcome

During the retrospective we followed a simple "What went well/What went wrong/what to improve" categorisation approach.
The following sections list "raw" items that were raised during the meeting:

### What went well

* Technical reports
* Agile development: Shifting focus for formal methods from Safety/Liveness proofs, to Voting string analysis to soundness property of test model
* Monthly wrap-up sessions with external stakeholders worked great. As well as the monthly videos
* Project is at the finish line
* Good complementary mix of skills on the team.
* Feedbacks between research, formalization, simulation, analysis, and testing
* Shared a lot of information and insights
* Literate Agda and drawing on tech reports worked well for the CIP.
* We avoided over-engineering and other activities that had low value added for providing evidence about the protocol It was good to stop at SRL 4.
* Good synergy w/in team
* Very productive workshops


### What went wrong (or not so well)

* Not much interest from the community + FUD & persistent misconceptions blurred the message
* Not sure Agda effort really pays off
* Handing over to IOE / Intersect isn't as easy as planned
* quickcheck-dynamic's methodology is misaligned with conformance testing of protocol implementation
* agda2hs and the Agda -> Haskell workflow are not sufficiently robust for use on the critical path
* Intersect wasn't ready to ingest results of the innovation stream.
* Soundness property proof is not yet finished / under-estimated proof effort
* Having both, the Haskell.Prelude as well as the Agda stdlib in the same project is a big hassle - decided too late in the project to have only one
* Could have started with the CPS


### What to improve

* Start from the beginning: "quantify" use cases
* Draw in folks outside of the team for some QA and review activities
* Start with CPS that can be shared with the community to get feedback
* Innovation role within the Intersect WGs
* Define early on what flavor of conformance tests are needed
* Write the CPS at the start and then start writing the CIP much sooner, because it highlights missing tasks early on.
* Redefined BRLs to fit innovation
* Use the formal language for the specification initially and do the proofs later, off of the critical path.
* And Test generators should be written in the formal language.
* Tighter feedback loop  (smaller more focused questions)
* Pairing / code review sessions for Agda
* Lessons learnt about DeltaQ

## Next Steps

Project is entering maintenance mode following the last Demo & Review meeting. As follow-up steps, we plan to:

1. Run an "Agda Retrospective" in Longmont
   * Reflect on different approaches used by different projects
   * Provide future guidelines about Formal Methods workflow w/in Innovation streams
   * Nudge people and teams to converge towards reasonably standardised methodology and tools (training, sharing libs, …)
2. Clarify boundaries of Innovation projects
   * What's the right input for innovation projects, or combination of inputs? Research papers, CPS, business requirements?
   * What are the right artifacts to handoff the project at completion?
   * Define a handover to IOE/Intersect process
   * Beware of the danger to be pulled into a production mindset
3. Three months chartering
   * More aggressive pruning of Question/Answer cycle within (and across?) innovation projects
   * "If we don't cancel anything, we are not taking enough risk"
4. Redefine BRLs (Business Readiness Level) to fit innovation projects
   * We need more hands-on people to identify use cases and interact with the community/users/ customers
   * DevRel role able to quickly build PoCs and sketch usages in the wild could be the vanguard to more structured product work
   * Most innovation projects are essentially features for our products, or proposals to improve Cardano. They are not standalone products that can have a meaningful business plan.
5. Provide a more focused post-mortem or lessons learned analysis about DeltaQ Software Development methodology
