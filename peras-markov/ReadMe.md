# Markov-chain computations of adversarial scenarios

Run Markov-chains simulations of the Peras pre-alpha protocol for adversarial scenarios.

#### To-do list

- [ ] Unit tests for adversarial behavior
- [ ] Statistical tests for adversarial strategies
- [ ] Include block-diffusion Δ
- [ ] Renormalize honest probabilities to account for short honest forks
- [ ] More than two chains
- [ ] Optimized computation on GPUs


## Adversarial behaviors

Adversarial behaviors can be customized by supplying a YAML file to the `--behavior-file` CLI option.

The file [honest-behavior.yaml](./honest-behavior.yaml) represents an adversary who always behaves honestly:

```console
$ cat honest-behavior.yaml

adverseVoting: AlwaysVote
adverseRevelation: AlwaysReveal
adverseAdoption: AdoptIfLonger
adverseBlocks:
  tag: PromptBlocks
adverseCertification: PromptVotes
addverseSplitting:
  tag: NoSplitting
```

In contrast, the file [private-chain-behavior.yaml](./private-chain-behavior.yaml) represents an adversary who builds their chain in private and who never votes for the honest chain.

```console
$ cat private-chain-behavior.yaml

adverseVoting: VoteForAdversary
adverseRevelation: NeverReveal
adverseAdoption: NeverAdopt
adverseBlocks:
  tag: PromptBlocks
adverseCertification: PromptVotes
addverseSplitting:
  tag: NoSplitting
```

The following behaviors are available:

- `adverseVoting`
    - `NeverVote`: the adversary never votes for a block.
    - `AlwaysVote`: the adversary always votes honestly.
    - `VoteForAdversary`: the adversary only votes for blocks on their preferred chain.
- `adverseRevelation`
    - `NeverReveal`: the adversary keeps their chain private.
    - `AlwaysReveal`: the adversary honestly reveals their chain.
    - `RevealIfLonger`: the adversary only reveals their chain to honest parties if it is weightiest chain.
- `adverseAdoption`
    - `NeverAdopt`: the adversary never adopts the honest chain.
    - `AdoptIfLonger`: the adversary adopts the honest chain if it is weightiest.
- `adverseBlocks`
    - `PromptBlocks`: the adversary honestly diffuses the blocks they forge.
    - `DelayBlocks Int`: the adversary waits the specified number of blocks before diffusing a block they forge.
- `adverseCertification`
    - `PromptVotes`: the adversary honestly diffuses the votes they cast.
    - `DelayVotes`: the adversary waits until just before the expiration time before diffusing a vote they cast.
- `adverseSplitting`
    - `NoSplitting`: the honest and adversarial nodes can communicate with one another throughout the simulation.
    - `MkAdverseSplit Slot Slot`: the honest and adversarial nodes do not communication with one another during the specified (inclusive) slot interval.


## Help

```console
$ cabal run exe:peras-markov -- --help

peras-markov: simulate Peras protocol using Markov chains

Usage: peras-markov [--version] COMMAND

  This command-line tool runs Markov-chain simulations of the Peras protocol.

Available options:
  -h,--help                Show this help text
  --version                Show version.

Available commands:
  longer-chain             Compute the probability of a private adversarial
                           chain being longer than the honest one.
  margin-reach             Compute the probability distribution of the margin
                           and reach for a one-slot diffusion time.
  length-difference        Compute the probability distribution of the length of
                           the honest chain minus the length of the adversarial
                           chain.
  lengths                  Compute the mean lengths of the honest and
                           adversarial chains.
  command-candidate-demo   Demonstrate a common-candidate simulation.
  separate-chains-demo     Demonstrate a separate-chain simulation.
```


## Probability of adversarial chain being longer than the honest one

```console
$ cat example-input.yaml 

α: 0.05
u: 150
a: 1500
r: 10
k: 25
b: 10
τ: 450
c: 600

$ cabal run exe:peras-markov -- longer-chain --slots 20 --param-file example-input.yaml --behavior-file private-chain-behavior.yaml --out-file example-output.tsv

$ cat example-output.tsv 

Slot    P(honest > adversary)   P(adversary >= honest)
1       4.7438621223469715e-2   0.9525613787765302
2       9.239536108283945e-2    0.9076046389171604
3       0.1350107637450336      0.8649892362549663
4       0.17541693986243181     0.8245830601375678
5       0.21373809335612082     0.7862619066438787
6       0.2500910143820277      0.7499089856179721
7       0.2845855406922287      0.7154144593077708
8       0.3173249894570455      0.6826750105429539
9       0.3484065614766823      0.6515934385233171
10      0.3779217195834542      0.6220782804165452
11      0.4059565429165054      0.5940434570834943
12      0.4325920586397119      0.567407941360287
13      0.4579045525697128      0.5420954474302867
14      0.4819658600841639      0.5180341399158352
15      0.5048436385899521      0.495156361410047
16      0.526601622746745       0.47339837725325395
17      0.5472998635625402      0.4527001364374588
18      0.5669949524043975      0.43300504759560177
19      0.5857402308989419      0.41425976910105744
20      0.6035859876332109      0.39641401236678836
```


## Common-candidate demo

```console
$ cabal run exe:peras-markov -- common-candidate-demo

Honest vs adversary length     Probability
--------------------------     -----------
LT & adversary candidate       3.0654488746085475e-2
EQ & adversary candidate       3.135862303919123e-2
GT & adversary candidate       0.7864335018756112
No adversary candidate         0.1515533863391272
```


## Separate-chains demo

```console
$ cabal run exe:peras-markov -- separate-chains-demo

# Symbolic and numeric computation of adversarial scenarios.


## Adversary builds a chain separately from the honest parties.

In this example the delta is the length of the honest chain minus the length
of the adversarial chain. We generate ten blocks.

Delta      Probability
-----      -----------
-10        q¹⁰
-8         10⋅p⋅q⁹
-6         45⋅p²⋅q⁸
-4         120⋅p³⋅q⁷
-2         210⋅p⁴⋅q⁶
0          252⋅p⁵⋅q⁵
2          210⋅p⁶⋅q⁴
4          120⋅p⁷⋅q³
6          45⋅p⁸⋅q²
8          10⋅p⁹⋅q
10         p¹⁰

Now substitute p = 2/3 and q = 1/3 into the result.

Delta      Probability
-----      -----------
-10        1/59049
-8         20/59049
-6         20/6561
-4         320/19683
-2         1120/19683
0          896/6561
2          4480/19683
4          5120/19683
6          1280/6561
8          5120/59049
10         1024/59049


## Adversary lengthens whichever of two chains is shorter.

In this example the delta is the difference in length between the two chains.
Here we bypass the symbolic computation and use double-precision floating-
point numbers. We generate ten blocks.

Delta      Probability
-----      -----------
-10        1.3006147436874456e-2
-8         6.177920032515366e-2
-6         0.1292485901539399
-4         0.154244779759183
-2         0.11172077427221455
0          6.0001016105268486e-2
2          0.11172077427221455
4          0.154244779759183
6          0.1292485901539399
8          6.177920032515366e-2
10         1.3006147436874456e-2

Repeat the computation for 2160 blocks and just print the result for when
delta is zero.

5.364242945540336e-60

We can sum all of the probabilities to check that they equal one and that
round-off errors are not a problem.

0.9999999999998728
```
