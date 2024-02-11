---
slug: 2
title: |
  2. Formal model in Agda is ground truth
authors: []
tags: [Accepted]
---

## Status

Accepted

## Context

* We are striving to build a "trail of evidence" from the abstract and formal work of researchers describing the algorithm in written words, to the actual implementation written in some programming language
* This trail starts at the formalisation of the algorithm and the various data structures, properties, components involved in a formal specification language namely [Agda](https://github.com/agda/agda)
* In order to ensure consistency across various tools and experiments while working on simulations, prototypes, test environments, etc. we need a "common language" from which to derive actual, language-specification implementations.

## Decision

* We will consider Agda code as our _source of truth_ to define types, data structures and properties relevant to the implementation of the Peras algorithm

## Consequences

* Actual data structures for particular languages (eg. Haskell or Rust) should be _generated_ from Agda code
* To simplify development, generated code can be checked in, properly packaged, and versioned to be used as a dependency by other components
* Generated code must _never_ be manually modified
