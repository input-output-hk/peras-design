# inspired by https://github.com/phadej/docker-haskell-example/blob/master/Dockerfile
FROM haskell:9.6.3 as build

RUN apt-get update -y && \
    apt-get upgrade -y && \
    apt-get install -y automake build-essential pkg-config libffi-dev libgmp-dev libssl-dev libtinfo-dev libsystemd-dev zlib1g-dev make g++ tmux git jq wget libncursesw5 libtool autoconf

# install libsodium
RUN git clone https://github.com/IntersectMBO/libsodium && \
    cd libsodium && \
    git checkout dbb48cc && \
    ./autogen.sh && \
    ./configure && \
    make && \
    make install && \
    cd ..

# install libblst
COPY ./install_libblst.sh /app/install_libblst.sh
RUN chmod +x /app/install_libblst.sh && /app/install_libblst.sh

# install libsecp256k
COPY ./install_libsecp256k1.sh /app/install_libsecp256k1.sh
RUN chmod +x /app/install_libsecp256k1.sh && /app/install_libsecp256k1.sh

COPY ./cabal.project /app/cabal.project

RUN mkdir /app/peras-hs && mkdir /app/peras-simulation && mkdir /app/peras-server

COPY ./peras-hs/peras-hs.cabal /app/peras-hs/peras-hs.cabal
COPY ./peras-simulation/peras-simulation.cabal /app/peras-simulation/peras-simulation.cabal
COPY ./peras-server/peras-server.cabal /app/peras-server/peras-server.cabal
COPY ./peras-delta-q/deltaq.cabal /app/peras-delta-q/deltaq.cabal
COPY ./test-demo/test-demo.cabal /app/test-demo/test-demo.cabal
COPY ./peras-markov/peras-markov.cabal /app/peras-markov/peras-markov.cabal

WORKDIR /app

RUN cabal update
RUN cabal build --dependencies-only all

COPY . /app

RUN cabal build all

# Make a final binary a bit smaller
RUN strip dist-newstyle/build/x86_64-linux/ghc-9.6.3/peras-server-0.1.0.0/x/peras-server/noopt/build/peras-server/peras-server

FROM ubuntu:22.04

WORKDIR /app
EXPOSE 8091

COPY --from=build /app/peras-server/* /app/
COPY --from=build /usr/local/lib/libsodium* /usr/local/lib/
COPY --from=build /usr/local/lib/libsecp256k* /usr/local/lib/
COPY --from=build /app/dist-newstyle/build/x86_64-linux/ghc-9.6.3/peras-server-0.1.0.0/x/peras-server/noopt/build/peras-server/peras-server /app

RUN ldconfig

ENTRYPOINT ["/app/peras-server"]
