# Peras server apps


## Peras simulation server


### Usage

```console
$ peras-server --help

peras-server: server Peras simulations

Usage: peras-server [--version] [--port PORT] 
                    [--username STRING --password STRING]

  This server provides Peras simulations.

Available options:
  -h,--help                Show this help text
  --version                Show version.
  --port PORT              Port on which the server listens.
  --username STRING        Authorized user.
  --password STRING        Password for authorized user.
```


### Security

- If not username/password pairs are supplied on the command line, then no authorization is required.
- The WebSocket connection does not require authorization.


### Example

```bash
cabal run exe:peras-server -- \
  --port 8092 \
  --username peras --password prototype \
  --username iohk  --password cardano
```


## Peras CLI app

Run a simulation from the command line.

```console
$ peras app --help

peras-app: simulate Peras protocol

Usage: peras-app [--version] --in-file FILE [--out-file FILE] 
                 [--trace-file FILE]

  This command-line tool simulates the Peras protocol.

Available options:
  -h,--help                Show this help text
  --version                Show version.
  --in-file FILE           Path to input YAML file containing initial simulation
                           configuration.
  --out-file FILE          Path to output YAML file containing final simulation
                           configuration.
  --trace-file FILE        Path to output JSON-array file containing simulation
                           trace.
```


### Example

```console
$ cat example-input.yaml

duration: 900
parties: 7
u: 20
a: 200
r: 10
k: 17
l: 10
tau: 3
b: 10
t: 15
committee: 5
delta: 0
activeSlots: 0.1
rngSeed: 42

$ peras-app --in-file example-input.yaml --out-file example-output.json --trace-file example-trace.jsonarray

$ head example-trace.jsonarray 

{"parameters":{"A":200,"B":10,"K":17,"L":10,"R":10,"T":15,"U":20,"Δ":0,"τ":3},"tag":"Protocol"}
{"roundNumber":0,"slot":1,"tag":"Tick"}
{"newChains":[],"newVotes":[],"partyId":1,"tag":"NewChainAndVotes"}
{"newChains":[],"newVotes":[],"partyId":2,"tag":"NewChainAndVotes"}
{"newChains":[],"newVotes":[],"partyId":3,"tag":"NewChainAndVotes"}
{"newChains":[],"newVotes":[],"partyId":4,"tag":"NewChainAndVotes"}
{"newChains":[],"newVotes":[],"partyId":5,"tag":"NewChainAndVotes"}
{"newChains":[],"newVotes":[],"partyId":6,"tag":"NewChainAndVotes"}
{"newChains":[],"newVotes":[],"partyId":7,"tag":"NewChainAndVotes"}
{"roundNumber":0,"slot":2,"tag":"Tick"}

$ jq . example-output.json | head 

{
  "diffuser": {
    "delay": 0,
    "pendingChains": {},
    "pendingVotes": {
      "915": [
        {
          "blockHash": "f9094b4c51114a53",
          "creatorId": 1,
          "proofM": "a0bae03967ffc586",
```
