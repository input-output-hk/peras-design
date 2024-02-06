# Simple Random Model for Building Intuition on Peras

```console
$ nix develop

$ cabal run exe:random-forks -- run 100

Parameters {peerCount = 10, downstreamCount = 3, maximumCurrency = 1000, activeSlotCoefficient = 0.2, meanCommitteeSize = 6, roundLength = 3}
Protocol {pSlotLottery = 4.462771441671176e-5, pCommitteeLottery = 1.8309033116110651e-3, roundDuration = 3}
Run `circo -Tpng -o 'peers.png' 'peers.dot'` to generate the diagram of peers.
Run `for i in chain-*.dot; do j=${i%%.dot}.png; dot -Tpng -o $j $i; done` to generate diagrams of chains.

$ circo -Tpng -o 'peers.png' 'peers.dot'

$ for i in chain-*.dot; do j=${i%%.dot}.png; dot -Tpng -o $j $i; done
```

![chain-100.png](https://ipfs.functionally.io/ipfs/QmSczjj3K4qxGZLnGtTBPvSfFNN8xgCfJBUBPjMDvt66QZ/random-forks/chain-100.png)

![peers.png](https://ipfs.functionally.io/ipfs/QmSczjj3K4qxGZLnGtTBPvSfFNN8xgCfJBUBPjMDvt66QZ/random-forks/peers.png)
