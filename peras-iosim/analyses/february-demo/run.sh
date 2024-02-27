#!/usr/bin/env bash

cabal run exe:peras-iosim -- \
  --parameter-file network.yaml \
  --protocol-file protocol-peras.yaml \
  --trace-file trace-peras.txt \
  --result-file result-peras.json \
  --network-dot-file network.dot \
  --chain-dot-file chains-peras.dot

cabal run exe:peras-iosim -- \
  --parameter-file network.yaml \
  --protocol-file protocol-praos.yaml \
  --trace-file trace-praos.txt \
  --result-file result-praos.json \
  --network-dot-file network.dot \
  --chain-dot-file chains-praos.dot

for ext in svg png
do
  circo -T$ext -o network.$ext network.dot
  dot -T$ext -o chains-peras.$ext chains-peras.dot
  dot -T$ext -o chains-praos.$ext chains-praos.dot
done
