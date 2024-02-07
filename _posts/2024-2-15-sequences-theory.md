---
layout: blog-post
title: "A Theory of Sequences in cvc5"
date: 2024-2-15
math: true
excerpt_separator: <!--more-->
toc: true
author: Yoni Zohar
---

## Introduction

The theory of [sequences](https://cvc5.github.io/docs/cvc5-1.1.1/theories/sequences.html) in cvc5 is relatively new.
In essence, it is meant to model data structures such as `List` in `Java`, or `std::vector` in `c++`.
Unlike the theory of [arrays](https://smtlib.cs.uiowa.edu/theories-ArraysEx.shtml), which is actually
a theory of maps, the theory of sequences is very rich, and allows, in addition to array-like
read and write operations, also operators such as concatenation, sub-list, length, and more.

## Motivation
The idea of having a specialized theory for 
sequences [has been around before](https://www.researchgate.net/publication/229069636_An_SMT-LIB_Format_for_Sequences_and_Regular_Expressions).
However, it was recently revisited, generalized, and expanded,
following a fruitful collaboration between members of the cvc5 team and the
[Move-Prover](https://github.com/move-language/move/tree/main/language/move-prover) 
team at Meta.

The Move Prover is a formal verification tool for smart contracts
written in the Move language. These are programs that are meant
to run on the blockchain, and are written in a resource-aware manner.
Given a program and a specification, the Move Prover tries
to determine whether the program meets the specification.
It does so by translating both the program and the specification into
an SMT-LIB query, which is unsatisfiable if and only if the 
program meets its specification.
This translation is based on various theories. 

Originally, the main theories that were responsible for the encoding of 
Move's data structures were the theory of [datatypes](https://cvc5.github.io/docs/cvc5-1.1.1/theories/datatypes.html) 
and the theory of [arrays](https://smtlib.cs.uiowa.edu/theories-ArraysEx.shtml).
However, as it turned out, this encoding was not efficient enough, as it involved many quantifiers.
A large portion of these quantifiers originated from the need to extend the theory of arrays,
which only allows to read and write from an array,
with richer operators, such as computing the length, concatenating, and more.
This realization led to the idea of introducing a new theory of sequences.

## Usage
The documentation for the theory of sequences can be found [here](https://cvc5.github.io/docs/cvc5-1.1.1/theories/sequences.html).
Roughly, it introduces a new sort called `Seq`, which is parametric.
For example, to define the sort of integer sequences, one would write (in SMT-LIB style) `(Seq Int)`.
Then, variables that represent sequences can be defined as usual.
For example, the following is a declaration of a variable that ranges 
over sequences of real numbers:
```
(declare-fun s1 () (Seq Real))
```

There are various operators that are supported, including
the representation of the empty sequence,
constructing a sequence from a single element,
concatenation of sequences, reading from and updating
sequences, reversing the order of the elements,
obtaining a sub-sequence, and more.

For example, the following formula (written again in SMT-LIB style) asserts
the existence of two non-empty sequences with equal lengths such that the first is 
the result of reversing the elements in the second,
as well as the existence of a third sequence, obtained 
from the first sequence by changing its first element to be the first 
element of the second sequence.

Of course, this formula is satisfiable, and `cvc5`
can quickly report satisfiability, and to provide
a satisfying model.

```
(set-logic QF_SLIA)
(declare-fun s1 () (Seq Int))
(declare-fun s2 () (Seq Int))
(declare-fun s3 () (Seq Int))

(assert (= (seq.len s1) (seq.len s2)))
(assert (and (distinct (seq.len s1) 0) (distinct (seq.len s2) 0)))
(assert (= s1 (seq.rev s2)))
(assert (= s3 (seq.update s1 0 (seq.unit (seq.nth s2 0)))))

(check-sat)
```

## Algorithms


## Implementation

## Conclusion



#### [Yoni Zohar](https://u.cs.biu.ac.il/~zoharyo1/) is a faculty member at Bar-Ilan University. His research interests are automated reasoning, satisfiability modulo theories, proof theory, and verification.
