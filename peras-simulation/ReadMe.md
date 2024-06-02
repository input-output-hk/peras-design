# Simulate and visualize the Peras protocol


## Simulation

The `peras-simulate` tool executes a Peras simulation.

- If invoked without any arguments, it prints an example simulation trace.
- If invoked with the `--in-file` option, it reads a [SimConfig](src/Peras/Abstract/Protocol/Network.hs) file, in JSON or YAML format. See [example-input.yaml](example-input.yaml).
    - The argument to the `--out-file` option specifies the file to write the final `SimConfig` to at the end of the simulation. To continue the simulation, edit the `finish` parameter to the ending time for the new simulation. See [example-output.yaml](example-output.yaml) for an example.
    - The argument to the `--trace-file` option specifies the file where the [PerasLog](src/Peras/Abstract/Protocol/Trace.hs) entries will be written as a JSON array. See [example-trace.jsonarray](example-trace.jsonarray) for an example.

```console
$ cabal run exe:peras-simulate -- --in-file example-input.yaml --out-file example-output.yaml --trace-file example-trace.jsonarray
```

### Usage

```console
$ cabal run exe:peras-simulate -- --help

peras-simulate: simulate Peras protocol

Usage: peras-simulate [--version] [--in-file FILE] [--out-file FILE] 
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

## Visualization

The `peras-visualize` tool visualizes the trace from a Peras simulation.

```console
$ cabal run exe:peras-visualize -- --trace-file example-trace.jsonarray --dot-file example.dot

$ dot -T svg -o example.svg example.dot
```

### Usage

```console
$ cabal run exe:peras-visualize -- --help

peras-visualize: visualize Peras simulation traces

Usage: peras-visualize [--version] --trace-file FILE [--dot-file FILE]

  This command-line tool visualizes Peras simulation traces.

Available options:
  -h,--help                Show this help text
  --version                Show version.
  --trace-file FILE        Path to input JSON-array file containing simulation
                           trace.
  --dot-file FILE          Path to output GraphViz DOT file containing
                           visualization.
```
