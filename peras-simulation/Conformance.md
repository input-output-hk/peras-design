# Conformance tests for Peras protocol implementations


The executable program `peras-conformance-tests` runs the Peras protocol conformance tests against an external implementation of the protocol. It writes messages to a pipe or socket and reads results from another pipe or socket. The Peras prototype/reference implementation `peras-simulation-pipe` is an example of such an external implementation.


## Example execution

First create named FIFOs for communicating between the conformance tester and the system under test.

```bash
mkfifo simin simout
```

Start the implementation being tested.

```bash
./peras-simulation-pipe < simin > simout
```

Run the tests.

```bash
peras-conformance-test -- --external-input=simin --external-output=simout
```

The output should look like the following:

```console
External node
  Implementation respects Peras protocol [✔]
    +++ OK, passed 100 tests.

    Action polarity (5050 in total):
    100.00% +

    Actions (5050 in total):
    35.84% +NewVote
    28.18% +NewChain
    27.27% +Tick
     8.71% +BadVote

Finished in 2.3098 seconds
```

Additional testing options are available:

```console
$ ./peras-conformance-test -- --external-input=simin --external-output=simout --help

Usage: peras-conformance-test [OPTION]...

OPTIONS
              --help              display this help and exit
              --ignore-dot-hspec  do not read options from ~/.hspec and .hspec
  -m PATTERN  --match=PATTERN     only run examples that match given PATTERN
              --skip=PATTERN      skip examples that match given PATTERN

RUNNER OPTIONS
        --[no-]dry-run          pretend that everything passed; don't verify
                                anything
        --[no-]focused-only     do not run anything, unless there are focused
                                spec items
        --[no-]fail-on=ITEMS    empty: fail if all spec items have been filtered
                                focused: fail on focused spec items
                                pending: fail on pending spec items
                                empty-description: fail on empty descriptions
        --[no-]strict           same as --fail-on=focused,pending
        --[no-]fail-fast        abort on first failure
        --[no-]randomize        randomize execution order
  -r    --rerun                 rerun all examples that failed in the previous
                                test run (only works in combination with
                                --failure-report or in GHCi)
        --failure-report=FILE   read/write a failure report for use with --rerun
        --rerun-all-on-success  run the whole test suite after a previously
                                failing rerun succeeds for the first time (only
                                works in combination with --rerun)
  -j N  --jobs=N                run at most N parallelizable tests
                                simultaneously (default: number of available
                                processors)
        --seed=N                used seed for --randomize and QuickCheck
                                properties

FORMATTER OPTIONS
  -f NAME  --format=NAME           use a custom formatter; this can be one of
                                   checks, specdoc, progress, failed-examples or
                                   silent
           --[no-]color            colorize the output
           --[no-]unicode          output unicode
           --[no-]diff             show colorized diffs
           --diff-context=N        output N lines of diff context (default: 3)
                                   use a value of 'full' to see the full context
           --diff-command=CMD      use an external diff command
                                   example: --diff-command="git diff"
           --[no-]pretty           try to pretty-print diff values
           --show-exceptions       use `show` when formatting exceptions
           --display-exceptions    use `displayException` when formatting
                                   exceptions
           --[no-]times            report times for individual spec items
           --print-cpu-time        include used CPU time in summary
  -p[N]    --print-slow-items[=N]  print the N slowest spec items (default: 10)
           --[no-]expert           be less verbose

OPTIONS FOR QUICKCHECK
  -a N  --qc-max-success=N  maximum number of successful tests before a
                            QuickCheck property succeeds
        --qc-max-discard=N  maximum number of discarded tests per successful
                            test before giving up
        --qc-max-size=N     size to use for the biggest test cases
        --qc-max-shrinks=N  maximum number of shrinks to perform before giving
                            up (a value of 0 turns shrinking off)

OPTIONS FOR SMALLCHECK
    --depth=N  maximum depth of generated test values for SmallCheck properties
```

In particular, the `--qc-max-success` flag will set the number of tests to be peformed.

```bash
./peras-conformance-test -- --external-input=simin --external-output=simout --qc-max-success=1000
```

Failures are reported along with the sequence of operations that led to them.

```console
External node
  Implementation respects Peras protocol [✘]     

Failures:

  app/Peras/Conformance/ExternalSpec.hs:20:7: 
  1) External node Implementation respects Peras protocol
       Assertion failed (after 8 tests and 1 shrink):
         do action $ Tick
            action $ NewChain [MkBlock {slotNumber = MkSlotNumber {getSlotNumber = 1}, creatorId = 1957821, parentBlock = "0000000000000000", certificate = Nothing, leadershipProof = "0004060708050806", signature = "0306030706030107", bodyHash = "0407040703050002"}]
            action $ Tick
            action $ Tick
            action $ Tick
            pure ()
         
         -- Actions:
         do
           action $ Tick
           action $ NewChain [Block {hash    = "0306030706030107"
                                     slot    = 1
                                     creator = 1957821
                                     parent  = "0000000000000000"
                                     cert    = Nothing}]
           action $ Tick
           action $ Tick
           action $ Tick
           -- round: 1
           -- expected: [Vote {round     = 1
                               creator   = 1
                               blockHash = "0306030706030107"
                               proofM    = "8cacfd4bd1f4a6b1"
                               signature = "8df58f3a86bba078"}]
           -- model state before:
             NodeModel
               {clock = 4
                allChains =
                  [Block {hash    = "0306030706030107"
                          slot    = 1
                          creator = 1957821
                          parent  = "0000000000000000"
                          cert    = Nothing}]
                  []
                allVotes = []
                allSeenCerts = Cert 0 ""}

  To rerun use: --match "/External node/Implementation respects model/" --seed 1591407443

Randomized with seed 1591407443

Finished in 0.7316 seconds
1 example, 1 failure
```


## Example requests and responses

The `peras-conformance-test` writes single-line JSON requests to the implementation being tested and reads single-line JSON responses from that implementation. There are three types of requests.

An `Initialization` request resets the state of the node. Typically, it looks something like the following, but as a single line of text.

```json
{
  "tag":"Initialize",
  "parameters":{"A":200,"B":10,"K":1,"L":1,"R":1,"T":0,"U":5,"Δ":0,"τ":1},
  "party":{"pid":1,"pkey":"0000000000000002710"},
  "slotNumber":1,
  "chainsSeen":[[]],
  "certsSeen":[{"blockRef":"","round":0}],
  "votesSeen":[]
}
```

This is typically followed by a series of `NewSlot` requests as follows, but again as a single line of text.

```json
{
  "tag":"NewSlot",
  "isSlotLeader":false,
  "isCommitteeMember":true,
  "newChains":[
    [
      {
        "bodyHash":"60010c5b69433df7",
        "certificate":{"blockRef":"c3efd7ac6c11c9c2","round":1},
        "creatorId":2771898,
        "leadershipProof":"26b22fe5576e79ea",
        "parentBlock":"029379c40624b874",
        "signature":"bc510004c4711a7e",
        "slotNumber":11
      },
      {
        "bodyHash":"a89dae6819b120b9",
        "certificate":null,
        "creatorId":1190686,
        "leadershipProof":"bcda134751f531e1",
        "parentBlock":"88af066e70385de7",
        "signature":"029379c40624b874",
        "slotNumber":3
      }
    ]
  ],
  "newVotes":[
    {
      "blockHash":"10474f4808696555",
      "creatorId":1604016,
      "proofM":"4530613f450d5720",
      "signature":"1f5f54220e6f5e06",
      "votingRound":1
    },
    {
      "blockHash":"10474f4808696555",
      "creatorId":1604016,
      "proofM":"5503736f532f3770",
      "signature":"4d4f3f340b7f1727",
      "votingRound":1
    }
  ]
}
```

The response to an `Initialization` or `NewSlot` request is a `NodeResponse` as follows, but again as a single line of text.

```json
{
  "tag":"NodeResponse",
  "diffuseChains":[
    [
      {
        "bodyHash":"60010c5b69433df7",
        "certificate":null,
        "creatorId":2771898,
        "leadershipProof":"26b22fe5576e79ea",
        "parentBlock":"029379c40624b874",
        "signature":"bc510004c4711a7e",
        "slotNumber":11
      },
      {
        "bodyHash":"a89dae6819b120b9",
        "certificate":null,
        "creatorId":1190686,
        "leadershipProof":"bcda134751f531e1",
        "parentBlock":"88af066e70385de7",
        "signature":"029379c40624b874",
        "slotNumber":3
      }
    ]
  ],
  "diffuseVotes":[
    {
      "blockHash":"cbac5639ad00f7de",
      "creatorId":1,
      "proofM":"18fbcfc22ef9d702",
      "signature":"fa23fb3d06ce755e",
      "votingRound":5
    }
  ]
}
```

Testing completes wiht a `Stop` request.

```json
{"tag":"Stop"}
```

An optional `Stopped` response is allowed.

```json
{"tag":"Stopped"}
```


## Schema


### `Block` object

| Key               | Value                   | Notes                                                              |
|-------------------|-------------------------|--------------------------------------------------------------------|
| `creatorId`       | number                  | The unique identifier of the party forging the block.              |
| `slotNumber`      | integer                 | The slot in which the block was forged.                            |
| `signature`       | string                  | Hexadecimal bytes of the block-producer's signature for the block. |
| `parentBlock`     | string                  | Hexadecimal bytes of the `signature` of the parent block.          |
| `certificate`     | `Cert` object or `null` | The certificate optionally included in a block.                    |
| `leadershipProof` | string                  | Hexadecimal bytes for the slot-leadership proof.                   |
| `bodyHash`        | string                  | Hexadecimal bytes with the hash of the block body.                 |


### `Cert` object

| Key        | Value   | Notes                                                              |
|------------|---------|--------------------------------------------------------------------|
| `round`    | integer | The voting round being certified.                                  |
| `blockRef` | string  | Hexadecimal bytes of the `signature` of the block being voted for. |


### `Initialize` object

| Key          | Value                     | Notes                                                                      |
|--------------|---------------------------|----------------------------------------------------------------------------|
| `tag`        | `"Initialize"`            |                                                                            |
| `parameters` | `Parameters` object       | The Peras protocol parameters.                                             |
| `party`      | `Party` object            | The party identifier for the subject under teste.                          |
| `slotNumber` | integer                   | The current slot number of the node clock.                                 |
| `chainsSeen` | array of array of `Block` | The chains the node has already seen; blocks are listed most recent first. |
| `certsSeen`  | array of `Cert`           | The certificates the node has already seen.                                |
| `votesSeen`  | arrof of `Vote`           | The votes the node has already seen.                                       |


### `NodeResponse` object

| Key             | Value                     | Notes                                                    |
|-----------------|---------------------------|----------------------------------------------------------|
| `tag`           | `"NodeResponse"`          |                                                          |
| `diffuseChains` | array of array of `Block` | Chains sent to the network for diffusion to other nodes. |
| `diffuseVotes`  | array of `Vote`           | Votes sent to the network for diffusion to other nodes.  |


### `Parameters` object


| Key | Value   | Notes                      |
|-----|---------|----------------------------|
| `A` | integer | The Peras $A$ parameter.   |
| `B` | integer | The Peras $B$ parameter.   |
| `K` | integer | The Peras $K$ parameter.   |
| `L` | integer | The Peras $L$ parameter.   |
| `R` | integer | The Peras $R$ parameter.   |
| `T` | integer | The Peras $T$ parameter.   |
| `U` | integer | The Peras $U$ parameter.   |
| `Δ` | integer | The network $Δ$ parameter. |
| `τ` | integer | The Peras $τ$ parameter.   |


### `Party` object

| Key    | Value  | Notes                                                                   |
|--------|--------|-------------------------------------------------------------------------|
| `pid`  | number | The unique numeric identifier for a party (i.e., block-producing node). |
| `pkey` | string | Hexadecimal bytes encoding properties of the party.                     |


### `Stop` object

| Key   | Value    |
|-------|----------|
| `tag` | `"Stop"` |


### `Stopped` object

| Key   | Value       |
|-------|-------------|
| `tag` | `"Stopped"` |


### `Vote` object

| Key           | Value   | Notes                                                              |
|---------------|---------|--------------------------------------------------------------------|
| `creatorId`   | integer | The unique identifier of the party voting.                         |
| `votingRound` | integer | The round for which the vote was cast.                             |
| `blockHash`   | string  | Hexadecimal bytes of the `signature` of the block being voted for. |
| `proofM`      | string  | Hexadecimal bytes for the committee-membership proof.              |
| `signature`   | string  | Hexadecimal bytes of the voter's signature for the vote.           |
