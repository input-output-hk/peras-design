# Peras simulation server


## Usage

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


## Security

- If not username/password pairs are supplied on the command line, then no authorization is required.
- The WebSocket connection does not require authorization.


## Example

```bash
cabal run exe:peras-server -- \
  --port 8092 \
  --username peras --password prototype \
  --username iohk  --password cardano
```
