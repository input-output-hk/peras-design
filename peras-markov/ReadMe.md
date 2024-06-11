# Markov-chain computations of adversarial scenarios

A work in progress.

```console
$ cabal run

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

Now substitute p = 2/3 and q = 1/3 pretty into the result.

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
