#!/bin/sh

: ${SECP256K1_VERSION:='v0.3.2'}
git clone --depth 1 --branch ${SECP256K1_VERSION} https://github.com/bitcoin-core/secp256k1
cd secp256k1
./autogen.sh
./configure --enable-module-schnorrsig --enable-experimental
make
make check
make install
