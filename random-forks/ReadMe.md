# Simple Random Model for Building Intuition on Peras

```console
$ nix develop

$ cabal run exe:random-forks

USAGE: random-forks DURATION PEER_FILENAME CHAIN_FILENAME

$ cabal run exe:random-forks -- 500 peers.dot chain.dot

$ circo -Tpng -o peers.png peers.dot

$ dot -Tpng -o chain.png chain.dot
```

![chain.png](https://ipfs.io/ipfs/Qme5KFUoNg7iDEQX84X6rU67YdYtMerp6Ywh574FKCTTCA)

![peers.png](https://ipfs.io/ipfs/QmTXidVC4bqUVc8mnvJbbFda8itBYuKNBhWahzWBN7zPQ3)
