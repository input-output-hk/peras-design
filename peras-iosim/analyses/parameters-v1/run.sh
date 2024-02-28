#!/usr/bin/env bash

echo "Boost,Seed,At Slot,Blocks,Slots,From Weight,To Weight" > rollbacks.csv

for b in $(seq 0 0.001 0.100)
do
  echo "boost = $b"
  sed -i -e "/^votingBoost:/s/.*/votingBoost: $b/" protocol.yaml
  SEED="$RANDOM"
  sed -i -e "/^randomSeed:/s/.*/randomSeed: $SEED/" network.yaml
  cabal run exe:peras-iosim -- --parameter-file network.yaml --protocol-file protocol.yaml --result-file result.json
  jq -r '.currentStates.[].rollbacks | add | select(. != null) | "'"$b,$SEED"'," + (.atSlot|tostring) + "," + (.blocks|tostring) + "," + (.slots|tostring) + "," + (.fromWeight|tostring) + "," + (.toWeight|tostring)' result.json >> rollbacks.csv
done
