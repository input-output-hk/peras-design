* [x] "sketches the architecture of the project" why are some lines black and some a bluish green?
* [x] It's not obvious to me that "Each vote is signed individually and the signature is checked by the receiving node" answers the "How can the voting state be bounded?" question.
* [x] My initial reaction to "Models and simulation show that votes need to be aggregated independently and certificates be part of "some" block bodies" is that this means I won't know which header chains have increased weight, since the certificate is only validatable once the block body is validated. So how will I know which blocks to download when I have multiple header chains? [After reading more, I'm starting to anticipate that certificates also propagate independently of block bodies?]
  * good remark: we should probably add the weight in the block header and let the node verify the certificate in the block body?
* [x] "Should vote contributions be incentivized?" "Probably not" That answer is unhelpfully opaque.
* [x] What is a "jugular experiment"?
* [x] Typo: "defusing" should be "diffusing"
* [x] These two seem to conflict somewhat: "Committee members are selected by a VRF-based sortition, its properties are exposed in the paper and overview" versus "Need to refine: Voting committee selection via sampling needs to define how to analyze the needed properties of the committee."
* [x] "Application identified?" "Done (Partner chains)" --- I'm surprised to see Partner Chains mentioned. Isn't "fast settlement" in and of itself a worthwhile application?
  * It would if there wasn't an associated cost, it was deterministic, and there wasn't any tradeoffs (eg. cooldown period)
* [x] What is the notation "? -> Tweag" supposed to mean?
* [x] This looks like a number of blocks "The duration of the cool-down period is roughly equal to + , where is the settlement parameter of Praos (e.g. 2160 blocks as of the time of this writing)." but the March 2024 pseudo-code instead specifies cooldown as a number of slots.

(tangent: I went and looked at the protocol Agda spec)
* [x] "Voting rounds are numbered 0, 1, 2, ..., and voting round corresponds to slots,,, ...,. No votes are cast in round 0, which is successful by definition." I think the Ts here are typos: they should be U, right?
* [x] "block_voted_for :  Block" --- it's a bit surprising to see Block here instead of Hash, but I can imagine this avoids having to carry a mapping in the environment, eg.
* [x] "Certify : Block -> Certificate -> Block" --- should that be Certify : Block -> Certificate -> Bool instead?
* [x] The definition of Chain is not visible in the rendered Markdown.
  * It did not seem that important, will add it back
* [x] Maybe I'm just not familiar enough with Agda, but what's the point of this unused b' binding? let b' = Certify b certseen? Why not eg use the ⊤ codomain instead of Block?
  * the pseudo-notation gloss over the details of what happens if the certification fails. It's a bit handwavy
* [x] My initial thought is that onPeerCertsChange doesn't ensure that there's a unique cert. I'm guessing: quorum/committee/etc chosen so that every possible cert in a round must be boosting the same block, and so all the valid certs in a round are effectively equivalent?
  * true. If you have a valid cert it's "impossible" another valid cert would point at another block as this would imply some double-voting
* [x] Is onPeerChainChange tacitly assuming that you always have a peer's cert before you have its chain? If not, then perhaps onPeerCertsChange needs to call onPeerChainChange, passing the most recently seen chain from the peer alongside its new cert?
  * yes. The whole dynamic of cert/vote diffusion will need to be refined
(end tangent)

* [x] "which sets the maximum number of slots for the network to produce k blocks" -- I suggest writing "to produce k subsequent blocks"
* [x] "In practice, the probability for a transaction to be rolled back after 20 blocks is 0.001%" --- we try to qualify such statements with a disclaimer: "if the parameters (including Delta, for example) are well-chosen, the network is healthy, the online/alert/etc honest stake dominates, and so on" or more opaquely, "while the network satisfies the Praos paper's theorems' preconditions", eg
  * I know, I was referring to the paper, will rephrase accordingly
* [x] Would it be possible to annotate the graph with how much adversarial stake is assumed, eg? (Instead of mentioning that in the subsequent section.)
* [x] "We also have anecdotal evidence from observations of the Cardano mainchain" --- it seems worth emphasizing that we have no reason to believe the (hypothetical) adversary has ever actually attempted to increase settlement times on mainnet Cardano, so the anecdotal observations and the preceding plot are not actually comparable.
  * I don't understand why they would not be
* [x] "While these numbers seem appealing" --- which numbers? The ones from the graph or the ones from the anecdote?
  * both?
* [x] A round length of "U = 10 slots" seems awfully short, ie lots of votes certs etc traffic.
  * yes, that's something we'll need to investigate
* [x] The Agda snippets in the "Domain model" section differ from those in the March 2024 (aka "latest") pseudo code, unless I'm mistaken. It seems worthwhile to add a remark acknowledging that.
* [x] I stumbled on "MAlonzo", since I don't know what that is.
* [ ] Unless I'm confused about bestChain, this property seems wrong to me "valid : ∀ (t : tT) (sl : Slot) → ValidChain (bestChain sl t)". It's quite easy to create an invalid chain that is better than any valid chain. ... Although maybe this is a clever way to avoid having to filter out invalid chains in this spec? ... Although, number 2: that would make it less obvious that the spec handles the (relatively boring) scenario where the best chain is invalid.
* [ ] I don't have the relevant context, but without it, I don't know how to interpret "there is no global Progess".
* [ ] "we only need to assert that before the clock reaches the next slot, all the deliverable messages in the global message buffer have been delivered." Does the deliverable filter here admit for modeling semi-synchrony, ie message delays up to Delta? ... Maybe "The party might be honest or adversarial, in the latter case a message will be delayed rather than consumed," clarifies that, but I'm not fluent enough in the DSL to see it in the type of the Deliver constructor. (Although the relation to Praos' Delta parameter is still not yet apparent.)
* [x] typo "paremeters" -> "parameters"
* [x] "Then using empiricalCDF computation" --- what is "empiricalCDF"? Just the cumulative sum over the samples? (I don't think I would be asking about this if the word weren't in the code font, eg.)
* [x] "If adding the certificate increases the size of the header beyond" --- The preceding text warned me already a few times, but there's still some cognitive dissonance reading sentences that seem to assume the header contains a cert.
* [ ] "uses pipelining to avoid having to confirm individually" --- just a heads up: there are two kinds of "pipelining" in Cardano. What you're referring to here is "mini protocol pipelining", which is different from "block diffusion pipelining" (which opportunistically avoids having to pay the validation time cost at every of hop along the path) :/
  * :thinking: can you elaborate on the latter?
* [x] "Depending on the value of the round length" -- another reminder that this seems to have been renamed to U in the latest psuedo code.
* [x] A broader recommendation: In my experience, we inherit terrible names from the researcher's algorithms. EG "k" for the "security parameter", and so on. During the genesis work, I started establishing better names (but still short). EG "sgen" versus "scg" to distinguish the two different "s" parameters from the Praos Chain Growth property versus the Genesis's density window definition. I would encourage you to to encourage the Innovation Team to introduce and enforce use of the "less mathy" but still not full CamelCase names sooner rather than later.
* [x] I recommend replacing "The vote diffusion should not be problematic" with "The vote diffusion will very likely be unproblematic" --- "should" at first sounds like normative/prescriptive text, a requirement, instead of an observation that justifies the rest of the sentence.
* [x] I think it would be helpful if "How long does it take for a transaction submitted to be settled" and the surrounding sentences were already explicitly clarifying that the settlement in question is observable. It's not just that users know "as of Peras, settlement is usually within 2 minutes" or whatever that delay is, but that their node can report that it validated a certificate that boosts a chain that includes their transaction, and so it is observably already as settled as if had been extended by k blocks.
* [x] An observation that is probably inconsequential: your "happy path" model assumes the submitted transaction and the eventual block take the same path to/from the minter, which isn't necessarily the case.
* [x] "Testing that uses the standard QuickCheck package is limited to the JSON serialization tests, such as golden tests [...]" --- what kind of golden tests involve randomized inputs?
* [x] As a US anglophone, I get distracted by "Shrinkage" (... blame Seinfield?)-- I would expect to see "Shrinking" instead.
  * this was written by another US anglophone person :smile:
* [x] Just FYI: "The following picture summarizes how the various parts of the testing framework for Peras are related:" --- this diagram is illegible for me, because it uses transparency and I view GitHub in "dark mode".
* [x] Why can't perform be generated? Is it because step function is not necessarly an executable spec?
* [x] This sentence "The simulator now only lightly uses IOSim's io-sim and io-classes, although it originally used them heavily." was not easy to unpack, even after reading the rest of the paragraph. It might be more meaningful (to me at least), if the text more explicitly clarifed what was removed to transition from "heavy use" to "light use".
* [ ] "Combined, these types allow a node to track the information ..." --- this paragraph prompted a thought. If you're using this code for simulation, then the "fully indexed total recall" optimizations described here sound uncharacteristic of the actual node implementation. Is that a desirable infidelity?
* [ ] "Client needs to Cancel and re-query when they want a different type of information" -- the real implementation doesn't cancel anything. Instead, it just discards the now-irrelevant responses, eg see https://github.com/IntersectMBO/ouroboros-consensus/blob/ddd6266f1d5a1a5eb05c756fcf8d5d95e1203c41/ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/MiniProtocol/ChainSync/Client.hs#L721-L728
* [x] "where [alpha] is the active slot coefficient" --- oh dear me please no. Use f or asc for the coefficient. We almost always use alpha for an amount of relative stake; usually the adversary's.
* [ ] I applaud this sentence! "Practically, this means that a random failure will occur about once in every ten or so invocations of the CI (continuous integration) tests, since each invocation executes 100 tests."
* [x] "Statistics for rollbacks, such as the ones shown below" --- in this diagram, should the y-axis "Blocks rolled back" instead be labeled "Weight rolled back"? If not, then I'm confused about how to interpret this plot.
* [ ] Also, same diagram: I wasn't expecting to see situations where the (unboosted) block count is very close to the slot count. Shouldn't that be an incredibly rare chain density? EG the dark blob that seems to be near the coordinate (45 slots, 22 blocks).
* [ ] "Only in cases of very sparse connectivity or slow message diffusion are longer forks seen." --- wouldn't an attack involving high adversarial stake also make deep forks more likely to occur?
* [ ] "Even though peras-iosim runs are not particularly fast, one probably does not need to parallelize them because typical experiments involve many executions of simulations, which means we can take advantage of CPU resources simply by running those different scenarios in parallel." --- excellent. Perhaps this should be foreshadowed in the preceding section that discusses parallelized discrete event simulations?
* [ ] "approximately 80% of the committee" --- and what is a typical committee size? Or more directly: how many votes are there in that 80%?
* [ ] "if I have certificate X for block A and a certificate Y for block B s.t. B [->] A" --- it's not obvious which block extends which from that arrow notation. But based on context I'm assuming you mean that A extends B?
(I'm now at the Recommendations)

* [x] "The analyses described in this report provide evidence that the Peras protocol is a viable addition to the Cardano blockchain in that it would significantly speed settlement (or, more precisely, rapidly decrease settlement-failure probabilities) without burdening the nodes with substantial additional computational or bandwidth requirements." --- At least after only my first read through, I would not immediately agree with this assertion. My current impression is that nearly every such analysis listed lots if incompletnesses, infidelities, used out-of-date protocols, etc. So this assertation currently seems illogical to me.
  * agreed, we should tone down the overly optimistic conclusion :)
* [x] (cont'd) For example, one concrete obstacle that comes to mind and I don't recall being obvious in this report: Does the math allow committee sizes to be so small that a certificate can easily fit within a block?
* [x] "The next steps for Peras center upon [...] (RFP) that includes acceptance criteria for implementations." --- based solely on this report, I think that is premature. I'd want to see something (presumably in this report) arguing about the absence of DoS vectors in the new mini protocols and databases/caches, such as vote/cert equivocation consuming too much CPU/memory.
* [x] "The executable specification could be packaged as a web-based, interactive simulator so that stakeholders can explore the behavior of Peras themselves and build intuition about the protocol." --- that sounds cute, but seems totally orthogonal to the release process.
