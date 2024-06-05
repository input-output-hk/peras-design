# Peras Formal Specification

The Peras protocol is being formalised using the [Agda](https://agda.readthedocs.io/en/v2.6.4.3/getting-started/what-is-agda.html) language and theorem prover.

An fully cross-referenced HTML rendering of the _literate Agda_ source files makes it easy to navigate the specification:

* [Small-steps Semantics](pathname:///agda_html/Peras.SmallStep.html) provides the foundations for the formalisation of the protocol's state machine and core types
* :hammer: [Properties](pathname:///agda_html/Peras.SmallStep.Properties.html) states and proves important safety and liveness properties about the protocol
* :hammer: [Analysis](pathname:///agda_html/Peras.SmallStep.Analysis.html) formalise the _voting string_ proof technique that's used in the original paper
* :hammer: [Execution](pathname:///agda_html/Peras.SmallStep.Execution.html) provides examples of _execution traces_ respecting the protocol's semantics
