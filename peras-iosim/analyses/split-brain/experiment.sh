#!/usr/bin/env bash

set -eo pipefail

function run {
  cabal run exe:peras-iosim -- \
    --protocol-file protocol-$1.yaml \
    --parameter-file network-$2.yaml \
    --result-file result-$1-$2.json \
    --chain-dot-file chain-$1-$2.dot
  for fmt in png svg
  do
    dot -T$fmt -o chain-$1-$2.$fmt chain-$1-$2.dot
  done
  echo "-----"
  echo "Protocol: $1"
  echo "Network: $2"
  ls -lh *-$1-$2.*
}

for p in praos peras
do
  for n in normal split
  do
    run $p $n &
  done
done
wait
