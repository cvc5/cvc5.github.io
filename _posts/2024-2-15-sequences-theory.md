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


## Usage


## Algorithms


## Implementation

## Conclusion


cvc5 is an SMT solver with support for many theories:
integers, reals, bit-vectors, algebraic datatypes, separation logic, sets,
bags, and more.
This means that is can find satisfying solutions for formulas involving these
kinds of objects.
In this post, I explain the process of adding a new theory to cvc5:
the theory of prime-order finite fields.

<!--more-->

This post serves as a record of the patches I made to cvc5 to add this theory,
and why I made them.
This post is not likely to be very comprehensible to someone who doesn't know
both how to use an SMT solver and a bit about how they are implemented.
For information about how they are implemented, the textbook "A Handbook of
Satifiability" is a good place to start.
For more information on how to use cvc5, check out our [examples](https://cvc5.github.io/docs/cvc5-1.1.1/examples/examples.html).

## Finite Fields

The theory we'd like to add is that of _finite fields_.
A finite field is a finite set of values with \\(\times\\) and \\(+\\) operations
which respect the usual properties:
associativity, inverses, commutativity, and
distributivity.

Our focus will be on *prime fields*,
which can be represented as integers modulo a fixed prime \\(p\\),
written
\\(\mathbb{F}_p\\)
or
\\(\mathbb{F}\\)
for brevity.

So, we'd like cvc5 to be able to determine things like this:

* that \\(x^2=-1\\) is unsatisfiable in \\(\mathbb{F}_3\\),
* that \\(x^2=1 \wedge x \ne 1 \wedge y^2 = x\\) is unsatisfiable in \\(\mathbb{F}_3\\), and
* that \\(x^2=y \wedge y^2 = 1\\) has solutions \\(y=1, x=-1\\) and \\(y=1,x=1\\) in \\(\mathbb{F}_3\\).

Our first task is to identify the sorts, operators, predicates, and constants
for this theory:

* Each prime field is its own sort.
* Within each sort, the two operators are \\(+\\) and \\(\times\\).
* The only predicate is equality, \\(=\\).
* The constants are just the numbers \\(\{0, 1, \ldots, p-1\}\\) (interpreted mod \\(p\\)).

## Concrete Values

We begin by creating a concrete value type for prime field elements.
This is just adding a file & class to `/util`. Roughly, the class looks like
this:

```cpp
class FiniteFieldValue {
 public:
  FiniteFieldValue(const Integer& val, const Integer& size);
  const Integer& getValue();
  const Integer& getFieldSize();
  friend bool operator==(const FiniteFieldValue&, const FiniteFieldValue&);
  friend bool operator!=(const FiniteFieldValue&, const FiniteFieldValue&);
  friend bool operator<(const FiniteFieldValue&, const FiniteFieldValue&);
  friend bool operator>(const FiniteFieldValue&, const FiniteFieldValue&);
  friend bool operator<=(const FiniteFieldValue&, const FiniteFieldValue&);
  friend bool operator>=(const FiniteFieldValue&, const FiniteFieldValue&);
  friend FiniteFieldValue operator+(const FiniteFieldValue&, const FiniteFieldValue&);
  friend FiniteFieldValue operator-(const FiniteFieldValue&, const FiniteFieldValue&);
  friend FiniteFieldValue operator-(const FiniteFieldValue&);
  friend FiniteFieldValue operator*(const FiniteFieldValue&, const FiniteFieldValue&);
  friend FiniteFieldValue operator/(const FiniteFieldValue&, const FiniteFieldValue&);
  FiniteFieldValue recip() const;
  // ...
};
```

&nbsp;

The PR that creates the class is [here][util]. In that PR, it's name is
`FiniteField`, which gets changed to `FiniteFieldValue` later.
Note that `Integer` is cvc5's internal multiprecision integer type.

## Theory Boilerplate

Next, we add boilerplate that defines a new theory in cvc5.
The PR is [here][boilerplate].

This boilerplate is organized around a shell-script
called the "kinds file". It declares basic theory and term
utilities.

Term utilities include:
* the finite field type definition
  * `FfSize`: a type for the cardinality of a field
  * `FiniteFieldProperties::computeCardinality`: computes the above
  * `FiniteFieldEnurator`: enumerates all elements of a field
* kind definitions:
  * `CONST_FINITE_FIELD`
    * this references `FiniteFieldValue` from the last PR
  * `FINITE_FIELD_MULT`
  * `FINITE_FIELD_ADD`
  * `FINITE_FIELD_NEG`

Each theory utility is materialized as a class. We'll discuss them in more
detail in a moment.

* `TheoryFiniteFieldsRewriter`: term rewriter
* `TheoryFiniteFields`: the theory solver
* the type checker:
  * `FiniteFieldConstantTypeRule`: for `CONST_FINITE_FIELD`
  * `FiniteFieldFixedFieldTypeRule`: for the other kinds (multiplication and addition)

The kinds file itself is a shell script that uses a number of cvc5-defined shell
functions to declare all of the above information.
So, essentially the file contains a bunch of pointers to difference C++
classes
that implement different parts of the theory.
Below, there is a rendering of the file with additional comments (and some omissions).

```bash
theory THEORY_FF \
    ::cvc5::internal::theory::ff::TheoryFiniteFields \
    "theory/ff/theory_ff.h"
typechecker "theory/ff/theory_ff_type_rules.h"
rewriter ::cvc5::internal::theory::ff::TheoryFiniteFieldsRewriter \
    "theory/ff/theory_ff_rewriter.h"

# declare a kind (FINITE_FIELD_TYPE) for the field sort itself
constant FINITE_FIELD_TYPE \
  struct \
  FfSize \
  "::cvc5::internal::FfSizeHashFunction" \
  "util/ff_val.h" \
  "finite field type"

# meta-data about the field sort
cardinality FINITE_FIELD_TYPE \
    "::cvc5::internal::theory::ff::FiniteFieldProperties::computeCardinality(%TYPE%)" \
    "theory/ff/theory_ff_type_rules.h"

enumerator FINITE_FIELD_TYPE \
    "::cvc5::internal::theory::ff::FiniteFieldEnumerator" \
    "theory/ff/type_enumerator.h"

well-founded FINITE_FIELD_TYPE \
    true \
    "(*cvc5::internal::theory::TypeEnumerator(%TYPE%))" \
    "theory/type_enumerator.h"

# declare a kind (CONST_FINITE_FIELD) for field values
constant CONST_FINITE_FIELD \
  class \
  FfVal \
  ::cvc5::internal::FfValHashFunction \
  "util/ff_val.h" \
  "a finite-field constant; payload is an instance of the cvc5::internal::FfVal class"

## declare other ff kinds and typing rules
operator FINITE_FIELD_MULT 2: "multiplication of two or more field elements"
operator FINITE_FIELD_NEG 1 "unary negation of a field element"
operator FINITE_FIELD_ADD 2: "addition of two or more field elements"

typerule CONST_FINITE_FIELD ::cvc5::internal::theory::ff::FiniteFieldConstantTypeRule
typerule FINITE_FIELD_MULT ::cvc5::internal::theory::ff::FiniteFieldFixedFieldTypeRule
typerule FINITE_FIELD_NEG ::cvc5::internal::theory::ff::FiniteFieldFixedFieldTypeRule
typerule FINITE_FIELD_ADD ::cvc5::internal::theory::ff::FiniteFieldFixedFieldTypeRule

endtheory
```

### The Rewriter

A rewriter extends `TheoryRewriter` and must implement:
`preRewrite` and `postRewrite`.
For now we implement both trivially, returning
`RewriteResponse(REWRITE_DONE, original_term)`.

### The Solver

The theory solver extends `Theory` and is considerably more complex.
Again, we implement it trivially for now:
in `void` methods we do nothing, and in methods that return something, we
return a default/null value.

One set of non-trivial methods is those that interact with the theory's
equality engine.
We create members of of type
`TheoryInferenceManager`
and
`TheoryEqNotifyClass`
, initialize them, and implement the following:

```cpp
bool TheoryFiniteFields::needsEqualityEngine(EeSetupInfo& esi)
{
  esi.d_notify = &d_eqNotify;
  esi.d_name = "theory::ff::ee";
  return true;
}

void TheoryFiniteFields::finishInit()
{
  Assert(d_equalityEngine != nullptr);

  d_equalityEngine->addFunctionKind(Kind::FINITE_FIELD_MULT);
  d_equalityEngine->addFunctionKind(Kind::FINITE_FIELD_NEG);
  d_equalityEngine->addFunctionKind(Kind::FINITE_FIELD_ADD);
}
```

&nbsp;

The first method says that we need an equality engine for out theory.
The second registers our function symbols with that engines (so it can do
congruence closure).

### The type-checker

The type checker is a collection of _type checking rules_.
Each rule is a class with a static, public method called `computeType`.
Here is an example: our type checking rule for addition and multiplication
nodes:

```cpp
TypeNode FiniteFieldFixedFieldTypeRule::computeType(NodeManager* nodeManager,
                                                    TNode n,
                                                    bool check)
{
  TNode::iterator it = n.begin();
  TypeNode t = (*it).getType(check);
  if (check)
  {
    if (t.getKind() != kind::FINITE_FIELD_TYPE)
    {
      throw TypeCheckingExceptionPrivate(n, "expecting finite-field terms");
    }
    TNode::iterator it_end = n.end();
    for (++it; it != it_end; ++it)
    {
      if ((*it).getType(check) != t)
      {
        throw TypeCheckingExceptionPrivate(
            n, "expecting finite-field terms from the same field");
      }
    }
  }
  return t;
}
```

&nbsp;

The arguments have the following meaning:

* `nodeManager` is a Node Manager that can be used to build terms.
* `n` is the node that we are type-checking
* `check` is true if we should check all children's type for consistency with
   this node's type. Otherwise, we should just compute this node's type.

## A Real Rewriter

Now, it's time to implement a non-trivial rewriter.
The PR is [here][rw].
A rewriter is responsible for normalizing and/or simplifying
the representation of theory terms.
Finite field terms
contain negations, additions, and multiplications. For example

$$ xy + (-xy) + 7 + (x + 2)(y + 3) + 2 $$

The goals for our rewriter are:
* normalize the \\(n\\)-ary associative-commutative operators (\\(+\\) and \\(\times\\))
  so that their arguments are always in the same order
* combine like terms in \\(+\\)
* replace negative with multiplication by \\(-1\\)

So we might rewrite the above to

$$ (x + 2)(y + 3) + 9 $$

The SMT-wide rewriter rewrites terms in a downward pass, followed by an upward
pass. For each term, it allows the theory for that term to specify a rewrite.
A theory specifies a rewriter by implementing a subclass of `TheoryRewriter`:

```cpp
class TheoryFiniteFieldsRewriter : public TheoryRewriter
{
 public:
  RewriteResponse postRewrite(TNode node) override;
  RewriteResponse preRewrite(TNode node) override;
};
```

&nbsp;

The downward pass hook is `TheoryRewriter::preRewrite`.
The upward pass hook is `TheoryRewriter::postRewrite`.
On our downward pass, we eliminate negation.
On our upward pass, we normalize \\(n\\)-ary operators and combine like terms.

## Statistics

Inside cvc5, a *statistics* system
is used to record and review dynamic information
about a solve attempt.
For example,
there are statistics that record how often each theory reports a conflict,
reports a lemma, and propagates a literal.
There are statistics that count total node allocations and
measure total solve time.
And many more.

Pre-emptively, we create an object to hold the finite field solver's
statistics, [here][stats].

## Theory-Internal Reasoning

At some point,
you need to implement the internal logic of your theory.
For a simple theory,
this means taking a conjunction of theory literals,
and determining:

* whether they are mutually satisfiable
* if so, a model: an assignment to theory variables that satisfies them all
* if not, an UNSAT core: a subset of
   literals that are also not mutually satisfiable.

In the case of finite-fields,
you can map the literals to set of multivariate polynomials \\(P\\)
such that a model corresponds to a common root \\(\vec x\\).
Each polynomial corresponds to one field literal;
if a subset of polynomials has no common roots,
then the corresponding subset of literals is an UNSAT core.

Anyways, our algebraic task is to find a common root for \\(P\\),
and if not, attempt to identify a root-free subset of \\(P\\).
To do this, we build a few pieces of machinery:

1. root-finding for a univariate polynomial ([PR][uniroots])
1. common root-finding for a set of multivariate polynomials ([PR][multiroots])
1. UNSAT cores for when a set of multivariate polynomials has no roots ([PR][cores])
1. An incremental common-root-finder/UNSAT core builder ([PR][gb])
   * Here, the input polynomial set \\(P\\) is incremental
      * you can push new polynomials, pop, and ask for a common root/UNSAT core
        at any time.

This machinery makes up the core logic of our theory. However, we have not yet
connected that logic to the Theory interface.

## A Sub-Theory Solver

The theory of finite fields is responsible for fields
of all sizes.
However, each field is independent of the others:
there are no conversion operators between fields,
and the only predicate (equality)
takes arguments of the same field.
Thus, we implement the theory of finite fields by implementing
a "sub-theory" that handles the field
\\(\mathbb{F}_p\\),
where \\(p\\) is fixed.

This class is worth discussing in more detail
because its interface foreshadows the
larger theory.
Here is the public interface:

```cpp
class SubTheory : protected EnvObj, protected context::ContextNotifyObj
{
 public:
  SubTheory(Env& env, FfStatistics* stats, Integer modulus);
  void preRegisterTerm(TNode term);
  void notifyFact(TNode fact);
  void postCheck(Theory::Effort effort);
  bool inConflict() const;
  const std::vector<Node>& conflict() const;
  const std::unordered_map<Node, Node>& model() const;
 private:
  // ...
};
```

&nbsp;

Now, let's discuss each method:

* `SubTheory(env, stats, modulus)`
  * the constructor; it takes:
    * a reference to the cvc5 environment (options, etc.),
    * a pointer to the statistics object we defined earlier (statistics will
       be shared across all sub-theories), and
    * `modulus`: the integer \\(p\\)
* `preRegisterTerm(term)`
  * called on all theory terms *before* they're in any fact
  * this does not include the facts themselves
    * for example `(= x y)` might not be pre-registered, but `x` and `y` will
       be
* `notifyFact(fact)`
  * assert a theory fact (\\(=\\) or \\(\ne\\)) (save it for `postCheck`).
* `postCheck(effort)`
  * called after some facts are notified
  * possible effort levels:
    * `STANDARD`: after Boolean constraint propagation in the SAT solver; a
       full Boolean assignment has not yet been found.
    * `FULL`: after a full Boolean assignment has been found
      * We do our work here, because
        * our theory is generally one of the slowest
        * our core reasoning (Groebner basis) is often more efficient with more information
    * `LAST_CALL`: after a model is available
  * this method doesn't return anything, but it does set internal state that
     can be measured by the methods below.
* `bool inConflict()`
  * report whether a conflict was found after the last postCheck
* `const std::vector<Node>& conflict()`
  * get the UNSAT core (only valid if a conflict has been found)
* `const std::unordered_map<Node, Node>& model()`
  * get the model (only valid if no conflict has been found)

We implement our subtheory in [this PR][subtheory],
with a few fixes in a [later PR][end].
Essentially, our implementation waits
for `FULL` effort, and then runs the common root finder
from the previous section.

## The Theory Solver

The final step is implementing the theory solver itself
and modifying cvc5's APIs and parser to make the
the theory solver accessible to cvc5's users.
The PR is [here][end].
This is the PR where we change the name of the class that represents finite
field values, to the diff is quite messy.
A cleaner (but incomplete) diff can be found [here][endsimple]:
the initial commit of the PR.

A laundry list of changes that we make:

* We implement `TheoryFiniteFields`:
  * essentially, the theory maintains a map from modulus to sub-theory
  * all methods forward their arguments to the appropriate sub-theory (or,
     create it if it doesn't exist yet)
* We create a new inference identifier for the theory's inference:
   `InferenceId::ARITH_FF`
  * To construct fine-grained proofs, we would refine this.
* We modify the cvc5 APIs (C++, Java, and Python) to allow field terms and
   predicates to be constructed.
* We modify the SMT-LIB parser to allows field terms and predicates to be
   parsed in SMT-LIB files.
* We add lots of tests
  * SMT2 regression tests
  * API examples
  * API tests

## A Final Change

In the foregoing, we developed a number of FF-internal data structures that
were incremental.
Specifically, we built data structures for incrementally building a set of polynomials,
finding their common roots,
and blaming the lack of common roots on a subset.
However, in our implementation of the sub-theory,
we didn't actually use these data structures very incrementally:
we pushed polynomials to them incrementally (as we we passed new FF facts),
but we only triggered a search for common roots at `FULL` effort.
Our choice to not use incrementality was guided by experiments
that showed it didn't improve performance.
In a [later PR][nonincremental], we made the data structures non-incremental,
which simplified the codebase significantly
and also improved performance a bit.
It didn't affect the interface between the theory of finite fields and the
rest of the SMT solver at all.

To give some more detail, before this patch, the core data structure was an
_incremental Ideal_:

```cpp
class IncrementalIdeal : EnvObj
{
 public:
  IncrementalIdeal(Env& env, CoCoA::ring polyRing);
  // Add new generators
  void pushGenerators(std::vector<CoCoA::RingElem>&& gens);
  // Remove the last batch of generators
  void pop();
  // Is the ideal the whole ring?
  bool idealIsTrivial();
  // For a trivial ideal, return a (sub)list of generator indices that generate it.
  const std::vector<size_t>& trivialCoreIndices();
  // For a trivial ideal, return a (sub)list of generators that generate it.
  std::vector<CoCoA::RingElem> trivialCore();
  // For a non-trivial idea, check whether there is a base-field variety member.
  bool hasSolution();
  // For a non-trivial idea with a base-field variety member, get it.
  const std::vector<CoCoA::RingElem>& solution();
 private:
  // ...
};
```

&nbsp;

After this patch, that data structure was eliminated, and replaced by a single
function that attempted to find a zero for a set of polynomials: returning
either a zero or a subset of the polynomials that had no zero.

[cvc5]: https://cvc5.github.io
[util]: https://github.com/cvc5/cvc5/pull/9026
[boilerplate]: https://github.com/cvc5/cvc5/pull/9059
[rw]: https://github.com/cvc5/cvc5/pull/9116
[stats]: https://github.com/cvc5/cvc5/pull/9173
[uniroots]: https://github.com/cvc5/cvc5/pull/9115
[multiroots]: https://github.com/cvc5/cvc5/pull/9181
[cores]: https://github.com/cvc5/cvc5/pull/9185
[guard]: https://github.com/cvc5/cvc5/pull/9198
[gb]: https://github.com/cvc5/cvc5/pull/9199
[subtheory]: https://github.com/cvc5/cvc5/pull/9210
[end]: https://github.com/cvc5/cvc5/pull/9218
[endsimple]: https://github.com/cvc5/cvc5/pull/9218/commits/af178dc12de75efa512af1a0c026bf07c8a5baef#diff-d3574afbd8bc203d5352f5e5100db19927dec39386d6c2a208613700e89ec1ea
[nonincremental]: https://github.com/cvc5/cvc5/pull/9486

Note: this content is cross-posted to our [wiki page](https://github.com/cvc5/cvc5/wiki/Adding-a-new-theory-to-cvc5) and to [Alex's blog](https://cs.stanford.edu/~aozdemir/blog/new-theory/).

#### [Alex Ozdemir](https://cs.stanford.edu/~aozdemir/) is a PhD student at Stanford in the [Center for Automated Reasoning](https://centaur.stanford.edu/) and the [Applied Cryptography group](https://crypto.stanford.edu/). His research uses ideas from cryptography, compilers, and verification to build programmable cryptosystems (such as zero-knowledge proofs and multi-party computations).
