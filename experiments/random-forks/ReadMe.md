# Simple Random Model for Building Intuition on Peras

```console
$ nix develop

$ cabal run

Parameters {peerCount = 10, downstreamCount = 3, maximumCurrency = 1000, activeSlotCoefficient = 5.0e-2, meanCommitteeSize = 6}
Protocol {pSlotLottery = 1.0258606257695924e-5, pCommitteeLottery = 1.8309033116110651e-3}
Run `circo -Tpng -o 'peers.png' 'peers.dot'` to generate the diagram of peers.

$ circo -Tpng -o 'peers.png' 'peers.dot'
```

![peers.png](peers.png)
