
---
layout: blog-post
categories: blog
excerpt_separator: <!--more-->
title: "Induction and Conjecture Generation in cvc5"
author: Kartik Sabharwal
date: 2024-10-03
---

This post is intended for users of SMT solvers who are interested in the automation of proofs by induction.
Such reasoning problems frequently arise in program verification, where data structures are modeled as datatypes and algorithms are modeled as functions on these datatypes.
We demonstrate cvc5's native support for structural induction over datatypes and its ability to synthesize lemmas that assist with such proofs, as described by Reynolds and Kuncak in [Induction for SMT Solvers][4].
<!--more-->

## A Preliminary Example

Consider a datatype 'Lst' whose terms represent finite lists of some fixed type  \\(X\\) .

$$\mathrm{Lst} = \mathrm{Nil} \mid \mathrm{Cons}(\mathrm{head}{:}X, \mathrm{tail}{:}\mathrm{Lst})$$

Also consider recursive axiomatizations of the functions 'length' and 'append'.

$$\begin{array}{lll}
 &\mathrm{length}(\mathrm{Nil}) & = 0 \\
\forall x{:}X, xs{:}\mathrm{Lst}.\,  &\mathrm{length}(\mathrm{Cons}(x, xs)) & = 1 + \mathrm{length}(xs) \\
 & & \\
\forall ys{:}\mathrm{Lst}.\,  &\mathrm{append}(\mathrm{Nil}, ys) & = ys \\
\forall x{:}X, xs, ys{:}\mathrm{Lst}.\,  &\mathrm{append}(\mathrm{Cons}(x, xs), ys) & = \mathrm{Cons}(x, \mathrm{append}(xs, ys)) \\
\end{array}$$

Let us prove the formula below.

$$\forall xs, ys{:}\mathrm{Lst}.\, \mathrm{length}(\mathrm{append}(xs, ys)) = \mathrm{length}(xs) + \mathrm{length}(ys)$$

One possible proof uses structural induction on  \\(xs\\) , which splits the goal into two subgoals, with one subgoal per Lst constructor.

$$\forall ys{:}\mathrm{Lst}.\, \mathrm{length}(\mathrm{append}(\mathrm{Nil}, ys)) = \mathrm{length}(\mathrm{Nil}) + \mathrm{length}(ys)$$

and

 \\(\forall x{:}X, xs, ys{:}\mathrm{Lst}.\\) 

$$\left( \begin{array}{lll}
 &\mathrm{length}(\mathrm{append}(xs, ys)) & = \mathrm{length}(xs) + \mathrm{length}(ys) \\
 \Rightarrow  &\mathrm{length}(\mathrm{append}(\mathrm{Cons}(x, xs), ys)) & = \mathrm{length}(\mathrm{Cons}(x, xs)) + \mathrm{length}(ys) \\
\end{array} \right)$$

The conjunction of the above subgoals implies, and is implied by, the original goal. The subgoal where  \\(xs\\)  is replaced with 'Nil' is commonly called the _base case_, whereas the subgoal in which  \\(xs\\)  is replaced with  \\(\mathrm{Cons}(x, xs)\\)  is called the _induction step_. In this proof, both the base case and the induction step can be proved using the axioms for 'length' and 'append' without resorting to a nested induction.

Concretely, the base case can be discharged as follows.

$$\begin{array}{clr}
 &\mathrm{length}(\mathrm{append}(\mathrm{Nil}, ys)) & \\
 =  &\mathrm{length}(ys) &[\text{by defn. of append}] \\
 =  &0 + \mathrm{length}(ys) &[\text{by properties of +}] \\
 =  &\mathrm{length}(\mathrm{Nil}) + \mathrm{length}(ys) &[\text{by defn. of length}] \\
\end{array}$$

The induction step can be discharged in a similar manner.

$$\begin{array}{clr}
 &\mathrm{length}(\mathrm{append}(\mathrm{Cons}(x, xs), ys)) & \\
 =  &\mathrm{length}(\mathrm{Cons}(x, \mathrm{append}(xs, ys))) &[\text{by defn. of append}] \\
 =  &1 + \mathrm{length}(\mathrm{append}(xs, ys)) &[\text{by defn. of length}] \\
 =  &1 + \mathrm{length}(xs) + \mathrm{length}(ys) &[\text{by induction hypothesis}] \\
 =  &\mathrm{length}(\mathrm{Cons}(x, xs)) + \mathrm{length}(ys) &[\text{by defn. of length}] \\
\end{array}$$

In the next section, we will translate this problem into SMT-LIB so that it may be evaluated on different SMT solvers.

## Induction and SMT Solvers

We can translate the definitions of 'Lst', 'length' and 'append', as well as the goal into SMT-LIB syntax, since this common standard supports the theories of datatypes, uninterpreted functions, and integer arithmetic.

```
;; length-append.smt2

;; Declare the abstract type 'X'
(declare-sort X 0)

;; Declare the 'Lst' datatype
(declare-datatype Lst
  ((Nil)
   (Cons (head X) (tail Lst))))

;; Declare and axiomatize 'append'
(declare-fun append (Lst Lst) Lst)

(assert 
 (forall ((ys Lst))
   (= (append Nil ys) ys)))

(assert 
 (forall ((x X) (xs Lst) (ys Lst))
   (= (append (Cons x xs) ys) (Cons x (append xs ys)))))

;; Declare and axiomatize 'length'
(declare-fun length (Lst) Int)

(assert
 (= (length Nil) 0))

(assert
 (forall ((x X) (xs Lst))
   (= (length (Cons x xs)) (+ 1 (length xs)))))

;; Assert the negation of the goal
(assert (not 
 (forall ((xs Lst) (ys Lst))
   (= (length (append xs ys)) (+ (length xs) (length ys))))))

;; Check satisfiability
(check-sat)
```

cvc5 and its predecessor cvc4 natively support induction on datatypes as well as on non-negative integers. As a result, cvc5 with structural induction enabled reports _unsat_ when run on length-append.smt2. Structural induction on datatypes is enabled with the option `--dt-stc-ind`. The intended invocation of cvc5 on length-append.smt2 is shown below:

```
$ cvc5 --force-logic=ALL --dt-stc-ind length-append.smt2
unsat
```

Most other SMT solvers, Z3 included, do not have native support for induction. They will time out or report _unknown_ run on length-append.smt2, no matter which options are enabled.

### A More Challenging Example

cvc5 can also automatically prove validity of the following formula which demands a more elaborate argument due to its use of commutativity.

$$\forall xs, ys{:}\mathrm{Lst}.\, \mathrm{length}(\mathrm{append}(xs, ys)) = \mathrm{length}(\mathrm{append}(ys, xs)) \quad [G_0]$$

Let us walk through one possible proof.

**Note.** We will use free variables (variables that are not explicitly bound by a quantifier) to denote fixed but arbitrary values.

**Step 1**  
Induct on  \\(xs\\)  to split the original goal  \\(G_0\\)  into two subgoals.

$$\forall ys{:}\mathrm{Lst}.\, \mathrm{length}(\mathrm{append}(\mathrm{Nil}, ys)) = \mathrm{length}(\mathrm{append}(ys, \mathrm{Nil})) \quad [G_1]$$

and

$$\begin{array}{clrl}
 &\big( \forall ys{:}\mathrm{Lst}.\,  &\mathrm{length}(\mathrm{append}(xs, ys)) & = \mathrm{length}(\mathrm{append}(ys, xs)) \big) \\
 \Rightarrow  &\big( \forall ys{:}\mathrm{Lst}.\,  &\mathrm{length}(\mathrm{append}(\mathrm{Cons}(x, xs), ys)) & = \mathrm{length}(\mathrm{append}(ys, \mathrm{Cons}(x, xs))) \big) \\
\end{array} \quad [G_2]$$

**Step 2**  
Induct on  \\(ys\\)  to split  \\(G_1\\)  into two further subgoals, each of which can be proved using just the definitions of 'length' and 'append'. Thus  \\(G_1\\)  is discharged, but it remains relevant as we will use it to discharge a subsequent subgoal in Step 3.

**Step 3**  
Only  \\(G_2\\)  remains to be proved. Treating its premise \\(\forall ys{:}\mathrm{Lst}. \mathrm{length}(\mathrm{append}(xs, ys)) = \mathrm{length}(\mathrm{append}(ys, xs))\\) as a background assumption, we induct on  \\(ys\\)  to split its conclusion into two more subgoals.

$$\mathrm{length}(\mathrm{append}(\mathrm{Cons}(x, xs), \mathrm{Nil})) = \mathrm{length}(\mathrm{append}(\mathrm{Nil}, \mathrm{Cons}(x, xs))) \quad [G_3]$$

and

$$\begin{array}{crl}
 &\mathrm{length}(\mathrm{append}(\mathrm{Cons}(x, xs), ys)) & = \mathrm{length}(\mathrm{append}(ys, \mathrm{Cons}(x, xs))) \\
 \Rightarrow  &\mathrm{length}(\mathrm{append}(\mathrm{Cons}(x, xs), \mathrm{Cons}(y, ys))) & = \mathrm{length}(\mathrm{append}(\mathrm{Cons}(y, ys), \mathrm{Cons}(x, xs))) \\
\end{array} \quad [G_4]$$

The first of these subgoals,  \\(G_3\\) , is a simple consequence of  \\(G_1\\) , which was proved in Step 2. The final subgoal  \\(G_4\\)  can be proved using the background assumption mentioned previously. This concludes the proof of  \\(G_0\\)  as a whole.

To verify that cvc5 is capable of independently following through with this line of reasoning, we supply it with the same definitions as before along with an encoding of the new goal.

```
;; length-flip-append.smt2

;; ...datatype and function definitions from length-append.smt2...

;; Assert the negation of the new goal
(assert (not 
 (forall ((xs Lst) (ys Lst))
   (= (length (append xs ys)) (length (append ys xs))))))

(check-sat) 
```

We can invoke cvc5 with the same options as in the previous example.

```
$ cvc5 --force-logic=ALL --dt-stc-ind length-flip-append.smt2
unsat
```

### Aside: Meta-Level Induction

How do interactive theorem provers such as [Dafny][2] and [HipSpec][3], that delegate reasoning to solvers with no native support for induction, prove formulas that are inductively valid?

They apply induction _at the meta level_. In other words, they heuristically apply an induction principle to split a goal into multiple subgoals and supply the resulting subgoals to their preferred automated theorem prover. The automated prover has a fair chance at discharging any subgoals that do not warrant induction.

Even systems that apply induction at the meta level may benefit from sending their subgoals to cvc5. As we have just seen, cvc5 has a chance at proving the subgoals that require a proof by induction in addition to those that do not.

## Conjecture Generation

In some situations even nested structural induction is insufficient to prove a valid goal. It is then necessary to assist the solver in its search for a proof by providing appropriate lemmas. To this end, cvc5 is able to perform a specific form of lemma synthesis. cvc5 uses heuristics to conjecture equalities between known terms, attempts to prove their validity by induction, then uses the proved conjectures as lemmas.

To see an example, consider the inductive datatype 'Nat.

$$\mathrm{Nat} = \mathrm{Zero} \mid \mathrm{Succ}(\mathrm{pred}{:}\mathrm{Nat})$$

Also consider two distinct but equivalent definitions of natural number addition.

$$\begin{array}{lll}
\forall x{:}\mathrm{Nat}.\,  &\mathrm{add}(x, \mathrm{Zero}) & = x \\
\forall x, y{:}\mathrm{Nat}.\,  &\mathrm{add}(x, \mathrm{Succ}(y)) & = \mathrm{Succ}(\mathrm{add}(x, y)) \\
 & & \\
\forall x{:}\mathrm{Nat}.\,  &\mathrm{deep\text{-}add}(x, \mathrm{Zero}) & = x \\
\forall x{:}\mathrm{Nat}.\,  &\mathrm{deep\text{-}add}(x, \mathrm{Succ}(\mathrm{Zero})) & = \mathrm{Succ}(x) \\
\forall x, y{:}\mathrm{Nat}.\,  &\mathrm{deep\text{-}add}(x, \mathrm{Succ}(\mathrm{Succ}(y))) & = \mathrm{Succ}(\mathrm{Succ}(\mathrm{deep\text{-}add}(x, y))) \\
\end{array}$$

We will prove that the definitions are in fact equivalent.

$$\forall x, y{:}\mathrm{Nat}.\, \mathrm{add}(x, y) = \mathrm{deep\text{-}add}(x, y)$$

A pen-and-paper proof might use a single course-of-values induction on  \\(y\\)  to prove the goal. However cvc5 lacks native support for course-of-values induction, as this would allow the active quantifier instantiation strategy to influence the effectiveness of the induction. Therefore the solver attempts a proof using successive weak structural induction. Even in the absence of conjecture generation, cvc5 is able to discharge all subgoals except for the following pair.

$$\begin{array}{crl}
 &\mathrm{add}(\mathrm{Zero}, y) & = \mathrm{deep\text{-}add}(\mathrm{Zero}, y) \\
 \Rightarrow  &\mathrm{add}(\mathrm{Zero}, \mathrm{Succ}(y)) & = \mathrm{deep\text{-}add}(\mathrm{Zero}, \mathrm{Succ}(y)) \\
\end{array}$$

and

$$\begin{array}{crl}
 &\big( \forall y{:}\mathrm{Nat}.\, \mathrm{add}(x, y) &= \mathrm{deep\text{-}add}(x, y) \big) \\
 \Rightarrow  &\mathrm{add}(\mathrm{Succ}(x), y) & = \mathrm{deep\text{-}add}(\mathrm{Succ}(x), y) \\
 \Rightarrow  &\mathrm{add}(\mathrm{Succ}(x), \mathrm{Succ}(y)) & = \mathrm{deep\text{-}add}(\mathrm{Succ}(x), \mathrm{Succ}(y)) \\
\end{array}$$

This pair of subgoals shares a common feature that hinders cvc5's default proof strategy. Namely in either subgoal, the arguments to 'deep-add' in the conclusion do not align with the arguments to 'deep-add' in the premises. To make progress in the proof the solver may be provided a lemma that aligns the arguments to 'deep-add' in the conclusion with those in the premises. Once cvc5's conjecture generation module is enabled, the solver can automatically conjecture and prove a sufficient lemma, which is

$$\forall x, y{:}\mathrm{Nat}.\, \mathrm{deep\text{-}add}(x, \mathrm{Succ}(y)) = \mathrm{Succ}(\mathrm{deep\text{-}add}(x, y))$$

Equipped with this lemma, cvc5 can discharge the extant subgoals as follows.

$$\begin{array}{clr}
 &\mathrm{add}(\mathrm{Zero}, \mathrm{Succ}(y)) & \\
= &\mathrm{Succ}(\mathrm{add}(\mathrm{Zero}, y)) &[\text{by defn. of add}] \\
= &\mathrm{Succ}(\mathrm{deep\text{-}add}(\mathrm{Zero}, y)) &[\text{by premise}] \\
= &\mathrm{deep\text{-}add}(\mathrm{Zero}, \mathrm{Succ}(y)) &[\text{by lemma}] \\
\end{array}$$

and

$$\begin{array}{clr}
 &\mathrm{add}(\mathrm{Succ}(x), \mathrm{Succ}(y)) & \\
= &\mathrm{Succ}(\mathrm{add}(\mathrm{Succ}(x), y)) &[\text{by defn. of deep-add}] \\
= &\mathrm{Succ}(\mathrm{deep\text{-}add}(\mathrm{Succ}(x), y)) &[\text{by premise}] \\
= &\mathrm{deep\text{-}add}(\mathrm{Succ}(x), \mathrm{Succ}(y)) &[\text{by lemma}] \\
\end{array}$$

This concludes the proof that 'add' and 'deep-add' are equivalent.

Our intended encoding of the above example in SMT-LIB syntax is shown below.

```
;; deep-add.smt2

;; Declare the 'Nat' datatype
(declare-datatype Nat
  ((Zero)
   (Succ (pred Nat))))

;; Declare and axiomatize 'add'
(declare-fun add (Nat Nat) Nat)

(assert
 (forall ((x Nat)) 
   (= (add x Zero) x)))

(assert
 (forall ((x Nat) (y Nat)) 
   (= (add x (Succ y)) (Succ (add x y)))))

;; Declare and axiomatize 'deep-add'
(declare-fun deep-add (Nat Nat) Nat)

(assert
 (forall ((x Nat)) 
   (= (deep-add x Zero) x)))

(assert
 (forall ((x Nat)) 
   (= (deep-add x (Succ Zero)) (Succ x))))

;; The pattern annotating this quantifier is instrumental for
;; conjecturing and proving an appropriate lemma 
(assert
 (forall ((x Nat) (y Nat)) (! 
   (= (deep-add x (Succ (Succ y))) (Succ (Succ (deep-add x y))))
 :pattern ((deep-add x (Succ (Succ y)))))))

;; Assert the negation of the goal
(assert (not
 (forall ((w Nat) (x Nat))
   (= (add w x) (deep-add w x)))))

;; Check satisfiability
(check-sat)
```

Conjecture generation in cvc5 is switched off by default, and can enabled with the command-line option `--conjecture-gen`. This is how we would invoke the solver on deep-add.smt2:

```
$ cvc5 --force-logic=ALL --dt-stc-ind --conjecture-gen deep-add.smt2
unsat
```

## Caveats

Though cvc5 can prove many inductive properties over datatypes, it is only fair to acknowledge that the efficacy of induction and conjecture generation depends on how the problem is posed to the solver. Specifically,

- cvc5 will only induct on variables of datatype sort bound using an existential quantifier that occurs positively, or a universal quantifier that occurs negatively. It will not induct on variables introduced with the 'declare-const' SMT-LIB command, even if they are of datatype sort.

- cvc5 inducts on variables according to the order in which they are bound. When dealing with an assertion of the form `(assert (not (forall ((b Nat) (a Nat)) (P a b))))`, the solver will induct on the variable `b` first and then on `a`.

- Functions defined using the SMT-LIB 'define-fun-rec' command are treated differently than function symbols introduced with the SMT-LIB 'declare-fun' command and then axiomatized using universally quantified formulas. In the latter case it also matters which quantifier patterns are associated with the universally quantified axioms, as evidenced by the third axiom for 'deep-add' in our final example.

It also helps to keep in mind that cvc5 only generates equality conjectures between terms of datatype sort. Consequently the solver will not propose an equality conjecture between two terms of a primitive sort, such as 'Int' or 'Bool'.

## Conclusion

We have seen how cvc5 natively supports structural induction and is able to synthesize useful lemmas for induction proofs, and we hope that this encourages you to experiment with cvc5's features for inductive reasoning.

#### Kartik Sabharwal is a PhD student advised by Cesare Tinelli in the [Computational Logic Center](https://clc-uiowa.github.io/) at the University of Iowa.  His interests lie in induction and quantifier instantiation.

[1]: https://www.microsoft.com/en-us/research/wp-content/uploads/2016/12/krml218.pdf
[2]: https://dafny.org/dafny/
[3]: https://github.com/danr/hipspec
[4]: https://homepage.divms.uiowa.edu/~ajreynol/vmcai15.pdf
