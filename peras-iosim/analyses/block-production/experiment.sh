#/usr/bin/env bash

PERAS_IOSIM=../../../dist-newstyle/build/x86_64-linux/ghc-9.6.3/peras-iosim-0.1.0.0/x/peras-iosim/noopt/build/peras-iosim/peras-iosim

cat << EOI > tmp-results.csv
Seed,Active Slot Coefficient,End Slot,Total Stake,Node Stake,Blocks Produced
EOI

for i in {1..1000}
do

SEED=$RANDOM
TOTAL_STAKE=1000
END_SLOT=7200
ASC=0.05

cat << EOI > tmp-network.yaml
randomSeed: $SEED
peerCount: 1
downstreamCount: 0
totalStake: $TOTAL_STAKE
maximumStake: $TOTAL_STAKE
messageDelay: 0.35
endSlot: $END_SLOT
EOI

cat << EOI > tmp-protocol.yaml
protocol: PseudoPraos
activeSlotCoefficient: $ASC
EOI

echo "$i: $SEED"

"$PERAS_IOSIM" --parameter-file tmp-network.yaml --protocol-file tmp-protocol.yaml --result-file tmp-result.json

jq -r '.currentStates.N1 | "'"$SEED","$ASC","$END_SLOT","$TOTAL_STAKE"',\(.stake),\(.preferredChain.blocks|length)"' tmp-result.json >> tmp-results.csv

done

sort -ur tmp-results.csv > results.csv
