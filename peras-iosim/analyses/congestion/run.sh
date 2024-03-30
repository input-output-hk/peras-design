#!/usr/bin/env bash

echo
rm stats.jsonarray
for la in 250000 500000 750000 1000000
do
  for bw in 50 20 10 5 2 1
  do
    echo $'\r'"la = $la, bw = $bw                 "
    sed -i -e "/^messageLatency:/s/:.*$/: $la/" -e "/^messageBandwidth:/s/:.*$/: $bw/" small-network.yaml
    cabal run exe:peras-iosim -- \
      --parameter-file small-network.yaml \
      --protocol-file pseudo-peras.yaml \
      --event-file events-$la-$bw.jsonarray \
      --verbose
    jq -c 'select(.contents.tag == "TraceStats") | .contents | {latency: '$la', bandwidth: '$bw', slot : .slot, node : .self, slotLeader : (.statistics.slotLeader | length), comitteeMember : (.statistics.committeeMember | length), cpuTime : .statistics.cpuTime, rxBytes : .statistics.rxBytes, txBytes : .statistics.txBytes, votingAllowed : (.statistics.votingAllowed | length), rollback : (.statistics.rollbacks | length)}' events-$la-$bw.jsonarray >> stats.jsonarray
  done
done
echo "                                   "
mlr --j2c cat < stats.jsonarray > stats.csv
