---
layout: blog-post
categories: blog
excerpt_separator: <!--more-->
title: "Interfaces for Understanding cvc5"
author: Andrew Reynolds
date: 2024-04-15
---

## The information gap in SMT solvers

State-of-the-art SMT solvers like cvc5 can be used to solve constraints in a growing number of application domains.
These applications often rely on constraints in undecidable logics, for example logics with quantified formulas, non-linear arithmetic and strings.
While there are no termination guarantees for such constraints, SMT solvers are nevertheless surprisingly effective at solving constraints in these logics.

In a perfect world, SMT solvers can be seen as black boxes that reliably respond to every user query in a reasonably small amount of time.
However, due to the increased complexity of constraints handled by SMT solver, this is far from a guarantee.
The solver may return "unknown", or depending on the patience of the user may be perceived as "going off into the woods".
It can be highly frustrating to users, since seemingly no information can be extracted when the solver times out.
In fact, it has been said that users of SMT solvers spend a *majority* of their time dealing with the case where the solver is unsuccessful.

This blog post focuses on improving the user experience of SMT solvers.
In particular, we focus on bridging the information gap between users and the internals of cvc5, particularly for when it is unable to solve a user query in a reasonable amount of time.

Many of the features explained in this post were originally used by cvc5 developers for purposes of internal debugging.
As these features matured, many were polished so that users could understand and benefit from them.
Users may be surprised to find out just how much information is available in the internals of cvc5.
If you are a user of cvc5, we welcome suggestions for new diagnostic information that would benefit your application.

In this blog post, we first recap the standard SMT-LIB interfaces for how to interact with the SMT solver when things go right, and then turn our attention to when things go wrong.

In the following, we frequently reference:
- SMT-LIB version 2.6 commands in the text interface (e.g. `(get-unsat-core)`).
- Command line options (e.g. `produce-unsat-cores`).
- Output tags, which are a family of command line options (e.g. `-o unsat-core-benchmark`). These do not impact the behavior of the solver apart from printing diagnostic information. These are documented here: https://cvc5.github.io/docs-ci/docs-main/output-tags.html.

While the discussion will focus on the command line interface and *.smt2 text interface, most of the features mentioned in this post are available in each of our APIs (C++, Java, Python).
Many of these features are new and are under active development.
All features are available in the latest unstable version of cvc5 on its main branch.

## Interfaces for when things go right

### Unsat cores

cvc5, like most SMT solvers, supports the SMT-LIB standard command `(get-unsat-core)`, which returns a subset of the user assertions that are sufficient for showing "unsat".
This may help narrow down what the relevant portion of the problem was that led to the refutation.
In cvc5, unsat cores are available immediately after an "unsat" response and when the option `produce-unsat-cores` is enabled.

```
% cat test.smt2
(set-logic ALL)
(set-option :produce-unsat-cores true)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (! (and (> x 2) (< x 0)) :named A))
(assert (! (< y 0) :named B))
(check-sat)
(get-unsat-core)

% cvc5 test.smt2
unsat
(
A
)
```

We support additional options pertaining to the way unsat cores are computed and printed:
- `minimal-unsat-cores`, which uses a greedy algorithm to drop assertions from the unsat core.
This option may induce additional performance overhead, but is useful if the user prioritizes smaller unsat cores.
The cores returned from this option are locally minimal (in that dropping any formula from the unsat core does not lead to an "unsat" response), although they are not guaranteed to be globally minimal.
- `print-cores-full`, which makes unsat cores can also be made agnostic to the smt2 attribute `:named`.
- `dump-unsat-cores`, which issues a command to the print the unsat core automatically after every unsatisfiable response.
- `-o unsat-core-benchmark`, which prints the unsat core as a standalone benchmark.
- `check-unsat-cores`, which internally double checks the correctness of the given unsat core.

cvc5 additionally supports more fine-grained variants of unsatisfiable cores which we describe in the following.

#### Unsat core of lemmas

cvc5 supports a custom SMT-LIB command `(get-unsat-core-lemmas)` which prints the theory lemmas that were relevant to showing unsatisfiable.
This is a list of valid formulas that were generated internally by theory solvers involving atoms not necessarily from the user input.
The lemmas used in the unsat core are availabe immediately after an "unsat" response and only when proofs are enabled (command line option `produce-proofs`).

```
% cat test.smt2
(set-logic ALL)
(set-option :produce-proofs true)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (! (and (> x 2) (< x 0)) :named A))
(assert (! (< y 0) :named B))
(check-sat)
(get-unsat-core-lemmas)

% cvc5 test.smt2
unsat
(
(or (not (>= x 3)) (>= x 0))
)
```

In the above example, a single theory lemma was generated which was required for showing the first assertion to be unsatisfiable.
Note that the literals `(>= x 3)` and `(>= x 0)` in this lemma correspond to the original two atoms after preprocessing.
The preprocessed form of the input is also available, which we will describe later in this post.

Theory lemmas may involve symbols that were introduced internally by cvc5 during solving, which we call "skolems".
A classic example is the "division by zero" skolem introduced to reason about the possibility of division with a zero denominator.
For details on all the documented skolem cvc5 supports, see: https://cvc5.github.io/docs-ci/docs-main/skolem-ids.html.

We also support dumping the unsat core along the lemmas used as a standalone benchmark via the output flag `-o unsat-core-lemmas-benchmark`.

#### Unsat core of instantiations

As a further refinement, one can ask specifically the shape of the quantifier instantiation lemmas used by cvc5 when solving a query.
These are available via the command line option `dump-instantitions`.
When proofs are enabled, this list is refined to only include the instantiations that were used in the proof of unsatisfiability.

```
% cat test.smt2
(set-logic UFLIA)
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (P x)))
(assert (or (not (P 3)) (not (P 4))))
(check-sat)

% cvc5 test.smt2 --dump-instantiations
unsat
(instantiations (forall ((x Int)) (P x))
  ( 3 )
  ( 4 )
)
```

A further refinement to this feature prints the "source" of the instantiation lemma, which is a unique identifier (which we call an "inference identifier") that indicates which part of cvc5's code base was responsible for the lemma.
This is available by the command line option `dump-instantiations-debug`.
In the future, we are planning to export more information about the meaning of the inference identifiers.

### Proofs

When cvc5 answers "unsat", a fine-grained account of its reasoning can be obtained via the SMT-LIB command `(get-proof)`.
Analogous to unsat cores, this requires the option `produce-proofs` to be enabled.
This section gives a cursory overview of the interface for getting proofs.

A proof is a step-by-step account of how a refutation can be derived from the input.
For documentation on the proof rules supported by cvc5, see https://cvc5.github.io/docs/cvc5-1.1.2/proofs/proof_rules.html.

The following outputs control how proofs are computed and printed:
- `proof-granularity=X` controls the granularity of the generated proof. This can range from allowing large informal "macro" steps to requiring each small-step theory rewrite to be justified.
- `check-proofs`, which runs an internal proof checker in cvc5 on the final proof.
- `proof-format=X` which impacts the format of the proof. By default, cvc5 generates proofs in the AletheLF format, which is a new proof format based on the SMT-LIB version 3.0 proposal. For details on AletheLF proofs in cvc5, see https://cvc5.github.io/docs/cvc5-1.1.2/proofs/output_alf.html.
- `dump-proofs`, which issues a command to the get the proof automatically after every unsatisfiable response.

cvc5 additionally provides interfaces for getting only part of the entire proof.
In particular, our `get-proof` command takes an optional "component" identifier, indicating the part of the proof that the user is interested in.
For instance, the user can ask for only the proofs of theory lemmas with the command `(get-proof :theory_lemmas)`.

We support an external proof checker `alfc` for the AletheLF format (see https://github.com/cvc5/alfc/blob/main/user_manual.md for details), and provide a script for getting started with this proof checker (https://github.com/cvc5/cvc5/blob/main/contrib/get-alf-checker).

### Models

cvc5 supports models via the SMT-LIB command `(get-model)` which is available immediately after a "sat" response.
This requires the option `produce-models` to be set to true.
Again, analogous to other features `dump-models` can be used to issue a command to print the model after every satisfiable response.
Models can be double checked for correctness internally using the option `check-models`.

#### Model cores

cvc5 supports a refinement to models where only the variables that were relevant for satisfying the user input.
We call this a "model core".
```
% cat test.smt2
(set-logic QF_UFLIA)
(set-option :produce-models true)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(assert (or (> z 5) (> y 5)))
(check-sat)
(get-model)

% cvc5 test.smt2 --model-cores=simple
sat
(
(define-fun y () Int 6)
)
```

In detail, a model core is an interpretation of a subset of the user variables where all extensions of that interpretation are also a model.
In the above example, if `y` is assigned the value `6`, then the input assertion evaluates to true no matter what the value of `x` or `z`.

## Interfaces for when things go wrong

Now that we have seen the information that is available after the SMT solver answers, consider the case where the solver times out or answers unknown.
Unfortunately, users are often unaware of how to obtain useful information in such cases.
In the following, we first focus on information that documents what the solver is doing. 
We then focus on newer features that are tailored towards aiding the user in assessing what went wrong, and in some cases, how to fix it.

### Incompleteness

When cvc5 answers "unknown", the user may ask for an explanation of why cvc5 gave up using the output tag `-o incomplete`.
Reasons can include resource limiting, incomplete heuristics for quantifier instantiation, unsupported combinations of theories, options misconfiguration, and so on.

> These reasons are not currently part of our API, but are documented internally here: https://github.com/cvc5/cvc5/blob/main/src/theory/incomplete_id.h.

### Timeout cores

cvc5 has experimental support for SMT-LIB command `(get-timeout-core)` which is analogous to unsat cores but is focused on queries that timeout.
In particular, a "timeout core" is a subset of the user input that is sufficient for making cvc5 timeout in a given timeout (configurable by `timeout-core-limit=X`).

$EXAMPLE$

cvc5 additionally supports a variant of the timeout core command where assumptions are provided.
In particular, the command `(get-timeout-core-assuming (a1 ... an))` asks cvc5 to find a subset of the formulas `a1, ..., an` that when combined with the input assertions cause a timeout.

$EXAMPLE$


When computing a timeout core, it may be the case that cvc5 stumbles upon a model or is able to prove unsat.
In these cases, it may respond "sat" or "unsat" to a `get-timeout-core` or `get-timeout-core-assuming` command.
In the latter case of "unsat", it will report the unsatisfiable core that it computed (which was a candidate timeout core that happened to be solved).

### Difficulty

cvc5 supports a notion of "difficulty" for input assertions, which is estimate of how likely the input assertion was the reason for cvc5 timing out.
The custom SMT-LIB command 

### Proof holes



### Abduction

A more ambitious line of work is to suggestion to the user how to repair a failed proof goal by synthesizing a formula, if true, would imply the user's proof goal.
This is called *abductive reasoning*, and can be used in

cvc5 supports a custom SMT-LIB command `get-abduct` which takes as arguments the name of the abduct and (optionally) a grammar of the abduct to synthesize.
It uses enumerative syntax-guided synthesis for deriving the abduct, which is then reported to the user as a `define-fun`.
Details on this algorithm can be found in [].

$EXAMPLE$

Abduction can 



### More information to understand what the Solver is doing

#### Statistics

The most basic form of information one can retrieve from cvc5 is its statistics.
These are dumped when cvc5 terminates when the option `stats` is enabled.
A more detailed account of statistics, including timing information and histograms of the inference identifiers used during solving is available when the option `stats-internal` is enabled.

### Partial information: learned literals, candidate model

When the SMT solver is unsuccessful at solving a given query, one logical question to ask is "what progress did the solver make?".
We can summarize this progress in two ways:
(1) Which formulas were learned during solving?
(2) What was the last candidate model that was tried?

#### Preprocessor

cvc5 implements a number of preprocessing passes that are applied to the input formulas prior to solving.
It is often useful to see how these passes modify the user input, prior to when the solving begins.

Let us revisit our earlier example:

```
% cat test.smt2
(set-logic ALL)
(set-option :produce-proofs true)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (! (and (> x 2) (< x 0)) :named A))
(assert (! (< y 0) :named B))
(check-sat)
(get-unsat-core-lemmas)

% cvc5 test.smt2 -o post-asserts
;; post-asserts start
(set-logic ALL)
(declare-fun y () Int)
(declare-fun x () Int)
(assert (>= x 3))
(assert (not (>= x 0)))
(assert (not (>= y 0)))
(assert true)
(check-sat)
;; post-asserts end
unsat

```

Here, we can see that cvc5 replaces strict inequalities with non-strict inequalities.

The set of input assertions, prior to preprocessing are also available via `-o pre-asserts`.
cvc5 also has other output tags that pertain to important things learned during preprocessing, 
for example, `-o subs` will output the substitutions corresponding to variable elimination inferred during preprocessing.

#### Lemmas

The main solving loop in SMT consists of a propositional SAT solver in combination with a set of theory solvers, the latter of which we call the "theory engine".
The latter sends a stream of theory lemmas to the SAT solver until the input and these lemmas is propositionally unsatisfiable, or a model is found.
The set of theory lemmas that are generated internally in cvc5 is available via `-o lemmas`.
This prints both 

#### Quantifier triggers and instantiations




#### Output tags for Syntax-guided Synthesis

cvc5 supports other kinds of constraints beside satisfiability.
In particular, we support syntax-guided synthesis problems (see ).
Our syntax-guided synthesis solver also supports diagnostic output flags, including `-o sygus` which output the list of candidate solutions as they are tried, `-o sygus-grammar` which outputs auto-generated grammars for functions-to-synthesize, and `-o sygus-sol-gterm` which indicates which production rules of a grammar were used in constructing the final solution.

### The Blessing and the Curse of Options

Finally, we remark that cvc5 has a vast array of configurable options that have accumulated over many years of development and research.
Options are categorized into the categories "common", "regular" and "expert", which classify whether the option should be consider robust for use in production settings.
This policy us furthermore be enforced automatically when using the (meta) option `safe-options`, which throws an exception if the user uses a combination of options that we consider unsafe.
More information for using cvc5 is available here: https://github.com/cvc5/cvc5/wiki/Fuzzing-cvc5.

In an ideal world, users of cvc5 should not need to worry about which options to use, and trust that the default configuration of cvc5 will always do the optimal thing.
For this purpose, cvc5 automatically configures its options based on the provided logic, as well as resolving any dependencies between options and reporting if there was an incompatibility of options.
The configuration routine is run prior to solving, after which options are fixed for the remainder of the run.
The output tag `-o options-auto` prints which options were automatically configured, as well as the reason for why the value of the option was modified.

```
```

Unfortunately, it is not always possible to infer optimal options, since it may be impossible to infer the user's intention and needs in their application.
We elaborate on this point specifically for logics involving quantifiers in the following.

#### Quantifiers

The flow chart below explains how to categorize the typical user of SMT quantifiers and which options to recommend in cvc5.

$DIAGRAM$

As future work, we would like to improve the experience of expert users that require suggestions for which options to use.
When all else fails, feel free to reach out to us via github issues or discussions.

