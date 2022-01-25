---
layout: default
---

# About cvc5

cvc5 is an efficient open-source automatic theorem prover for
[Satisfiability Modulo Theories (SMT)](
    https://en.wikipedia.org/wiki/Satisfiability_Modulo_Theories)
problems.
It can be used to prove the **satisfiability** (or, dually, the **validity**)
of first-order formulas in a large number of theories and their combination.
It further provides a [Syntax-Guided Synthesis (SyGuS)](https://sygus.org)
engine to synthesize functions with respect to background theories and their
combination.

cvc5 is the successor of [CVC4](https://cvc4.cs.stanford.edu) and is
intended to be an open and extensible SMT engine.
It can be used as a stand-alone tool or as a library, with essentially no limit
on its use for research or commercial purposes (see
[license](https://github.com/cvc5/cvc5/blob/master/COPYING)).
To contribute to cvc5, please refer to our [contribution
guidelines](https://github.com/cvc5/cvc5/blob/master/CONTRIBUTING.md).

cvc5 is a joint project led by Stanford University and the University of Iowa.



# Technical Support

For bug reports, please use the <a title="cvc5 bug tracking system"
href="https://github.com/cvc5/cvc5/issues" rel="nofollow">cvc5 issue
tracker</a>.

If you have a question, a feature request, or if you would like to contribute
in some way, please use the <a title="cvc5 discussions" href="https://github.com/cvc5/cvc5/discussions">discussions feature on the cvc5 GitHub repository</a>.



# Guidelines For Fuzzing cvc5

The development team of cvc5 is committed to ensure that its core
usage model (without experimental options) is extremely robust.
At the same time, our team is small and we have to set priorities,
including prioritizing user bugs over fuzzer bugs.

For fuzzing bugs, we ask you to follow this
[guidelines](https://github.com/cvc5/cvc5/wiki/Fuzzing-cvc5).
