FROM haskell:9.6.3

COPY . /app
WORKDIR /app

RUN cabal update && cabal build all

EXPOSE 8091

WORKDIR /app/peras-server

CMD cabal run peras-server
