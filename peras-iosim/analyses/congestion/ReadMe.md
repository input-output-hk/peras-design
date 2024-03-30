# Congestion Experiment

A coarse study to exercise peras-iosim in a simulation experiment involving network congestion.

- simulation/analysis workflow
- scalability and performance
- observability


## Configuration

We construct a full factorial experiment where bandwidth and latency are varied on a small network with semi-realistic Peras parameters. Each block has its maximum size.

- 250 nodes with fivefold connectivity
- ~25 committee members
- Full blocks (90.112 kB)
- Latency from 0.25 s to 1.00 s
- Bandwidth from 8 Mb/s to 400 Mb/s

The network configuration [small-network.yaml](small-network.yaml) is varied during the experiment, but the protocol parameters [pseudo-peras.yaml](pseudo-peras.yaml) remain constant.

```console
$ cat small-network.yaml

randomSeed: 13234
peerCount: 250
downstreamCount: 5
maximumStake: 1000
messageLatency: 1000000
messageBandwidth: 1
endSlot: 600

$ cat pseudo-peras.yaml 

activeSlotCoefficient: 0.10
roundDuration: 10
pCommitteeLottery: 0.00021
votingBoost: 0.25
votingWindow: [50, 1]
votingQuorum: 10
voteMaximumAge: 30
cooldownDuration: 5
prefixCutoffWeight:  10000000
```

## Running the experiment

The source code for the experiment is in the follow git patch: [congestion.patch.gz](congestion.patch.gz).

Execute [run.sh](run.sh) to run the simulations and collect the output in a file [stats.csv](https://ipfs.io/ipfs/QmWcUw2KZEN6UkazZALwvP9HYC4f3m9pV4S78FpPiG5n13).


## Caveats

- Memory pool and other non-block/non-vote messages not modeled
- February version of Peras protocol
- Simulation not validated - not suitable for making conclusions about Peras


## Analysis

The following R code is used to plot the results.

```R
require(data.table)
require(ggplot2)

raw <- fread("stats.csv")

results <- raw[,
  .(
    "RX [B]"=sum(as.numeric(rxBytes))
  ), 
  by=.(
    "Latency"=factor(paste(latency / 1000, "ms"), levels=c("1000 ms", "750 ms", "500 ms", "250 ms")), 
    "Bandwidth"=factor(paste(bandwidth * 8, "Mb/s"), levels=c("8 Mb/s", "16 Mb/s", "40 Mb/s", "80 Mb/s", "160 Mb/s", "400 Mb/s")), 
    "Slot"=slot
  )
][, 
  .(
    `Slot`,
    "Cumulative RX [MB]"=cumsum(`RX [B]`)/1000000
  ), 
  by=.(
    `Latency`, `Bandwidth`
  )
]

ggplot(results, aes(x=`Slot`, y=`Cumulative RX [MB]`)) +
  geom_line() +
  facet_grid(`Latency` ~ `Bandwidth`)
```


## Findings

- A threshold is readily detectable at a bandwidth of ~20 Mb/s.
- Non-block and not-vote messages such as those related to the memory pool must be accounted for in congestion.
- The event logging and statistics system easily supports analyses such as this.
- Data on node processing times is needed.

The following diagram shows the cumulative bytes received by nodes as a function of network latency and bandwidth, illustrating the ttheshold below which bandwidth is saturated by the protocol and block/vote diffusion.

![Cumulative bytes received by nodes as a function of network latency and bandwidth](congestion.png)
