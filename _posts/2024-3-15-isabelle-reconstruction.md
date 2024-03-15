---
layout: blog-post
categories: blog
excerpt_separator: <!--more-->
title: "Reconstructing cvc5 proofs in Isabelle/HOL- Part I: Isabelle"
author: Hanna Lachnitt
date: 2024-14-15
---

# Reconstructing cvc5 proofs in Isabelle/HOL- Part I: Isabelle

If you have used the cvc5 SMT solver before you know that it can solve many complicated problems fast, especially for the theories it supports! But can other programs profit from cvc5's efficiency too? And if so, how can cvc5 effectively communicate with these external tools? Could we use their feedback to increase our trust in cvc5's result even more?

<!--more-->

This blog post is the first in a series of two on improving proof automation in [Isabelle](https://isabelle.in.tum.de/) with SMT solvers. This part will give some background on Isabelle and describe the general approach we are using to integrate cvc5. If you are already familiar with Isabelle, feel free to skip ahead to [this section](#proof-automation-in-isabelle).

<div align='center'>
<img src="/assets/blog-images/2024-3-15-isabelle-reconstruction/IsabellePlusCvc5.svg" alt="isabellepluscvc5" class="center" width=80% />
</div>

## What is Isabelle?

Isabelle is an interactive theorem prover (also called proof assistant); a tool where human and machine work together to find proofs! Proofs to what you might ask? Isabelle uses a very expressive language that enables you to formalize almost any problem! It has been successfully used in various domains!  From the verification of the [seL4 microkernel](https://sel4.systems/) to the formalization of [pure math results](https://www.isa-afp.org/topics/), chances are that someone has already used Isabelle for it!

This has led to many nifty libraries and tools that you can use in Isabelle out of the box. For example, say you want to make sure that the quantum gate you defined is invertible or make some changes to your cryptographic standard and are worried that this could create bugs? Then, there are already many definitions and results proven in Isabelle that you can build on!

### Proofs in Isabelle

You can think of a proof in Isabelle as a little algorithm (we call this a tactic). This algorithm tells Isabelle how the problem can be solved by a list of steps.

<div align='center'>
<img src="/assets/blog-images/2024-3-15-isabelle-reconstruction/comic.png" alt="comic" class="center"/>
</div>

Think of it as writing a proof in math class in school. You'll have to convince your teacher that you have actually solved the problem and not just made a lucky guess. When you write your proof, you will have to state and justify all the steps you did to reach the result. Every step has to be explained in a way that your teacher can comprehend, and it also has to be detailed enough so that it is easy to verify its correctness.

For example, you might have proven something by contradiction or by induction before. Isabelle has an induction tactic as well as one that does case splits, and one that you can use to apply a previously proven fact. Another tactic called `simp`, automatically tries to simplify the goal as much as possible using previously proven statements and definitions. Unlike your pen and paper proof, Isabelle expects a formal proof where every step is well-defined. You cannot just skip steps by writing “exercise left to the reader” or “trivial”. However, the simplifier is already quite powerful and can solve many goals for you!

This is a small lemma in Isabelle that proves Gauss' sum formula. Don't worry if you don't understand every part of this lemma. It uses induction to solve that the sum of the numbers from $0$ to $n$ is $n*(n+1)/2$. Then, it uses the `simp` tactic to solve both base case and hypothesis. 

<div align='center'>
<img src="/assets/blog-images/2024-3-15-isabelle-reconstruction/lemmaGauss.png" alt="lemmaGauss" class="center" width=50% />
</div>

It might seem obvious, but this example shows that Isabelle provides a definition of natural numbers `nat` as well as operators such as addition, multiplication, and division on them that we are able to use here without defining them ourselves. 

In contrast to an automated theorem prover where you input your problem and get some output, the idea behind interactive provers is that both machine and human do what they are good at. The human has the creative idea on how to solve a problem, and the machine makes sure there are no errors and solves tedious parts of the proof itself. In this case the human might have the idea to solve this by induction, but the machine can deal with actually doing the calculations involved to solve the base case and finding out how to apply the induction hypothesis.

### Proof automation in Isabelle

But that's not all that Isabelle has to offer! You can ask Isabelle to help you to find the right lemmas and tactics you need to solve your goal. [Sledgehammer](https://isabelle.in.tum.de/dist/doc/sledgehammer.pdf) is a tool inside of Isabelle that will tackle your lemma automatically and suggest a proof (maybe by a tactic you have not known about before like `presburger` or `force`):

<div align='center'>
<img src="/assets/blog-images/2024-3-15-isabelle-reconstruction/IsabelleAutomation.png" alt="IsabelleAutomation" class="center"  width=80%/>
</div>

Sledgehammer has the ability to call external solvers. Here it called two solvers called zipperposition and vampire. It will encode the statement you want to prove in Isabelle (your current proof goal) into a format that these solvers can understand. It also includes some lemmas and facts that it thinks the solvers will need to solve the goal. For example, in this case it seems like there is already a lemma called `gauss_sum_nat` that shows something similar to our lemma and that we can use to prove the new goal.

Sledgehammer will call solvers repeatedly with different collections of lemmas. While this is often necessary to enable the solver to even find a proof before it reaches its resource limit, it has even more vital than just giving shortcuts. For example, a first-order logic solver has no concept of what a natural number is, so if that is important for the goal sledgehammer will have to include a definition in the facts it passes over to the solver.

SMT solvers like cvc5 have dedicated theory reasoning for a number of theories! This gives them an advantage for problems in these theories since they can apply dedicated decision procedures for each theory. Furthermore, Sledgehammer has to pass less lemmas on to the solver. This all provided that Sledgehammer translates every constant, type, and operator in Isabelle into the correct SMT-LIB constant, sort, and function.

<div align='center'>
<img src="/assets/blog-images/2024-3-15-isabelle-reconstruction/IsabelleAsksCvc5.svg" alt="IsabelleAsksCvc5" class="center" width=70%/>
</div>

Sledgehammer can already translate goals into SMT-LIB problems for some theories (see for example, this paper by [Blanchette et al.](https://doi.org/10.1007/s10817-013-9278-5)). 

## Trusting the untrustworthy? 

Exciting! So we can now use cvc5 to solve goals and Isabelle merely has to lean back and pass on the result to the user? Not quite...

Isabelle only uses a small kernel of inference rules and everything else has to be proven from them. This results in Isabelle's reasoning having a high trustworthiness attached to it. Therefore, Isabelle is quite skeptical when it comes to results proven outside of the solver that could endanger this trust. It will try and find its own proof internally.

Why did it call the external solvers then? Well, Isabelle's proof search is quite slow and it helps a lot to know which facts are needed to solve an open goal or even learning that the goal is indeed true. Isabelle will call solvers repeatedly trying to find the smallest set of facts needed to prove the goal (this is generally called the "unsat core" of the problem). As an optimization an external solver can also pass an unsat core to Isabelle directly.

This does work for a lot of problems but even knowing which facts are needed to prove a goal Isabelle might not find a proof on its own. In the following example only the two SMT solvers found a proof but Isabelle could still not use its powerful `metis` tactic to do the same.

<div align='center'>
<img src="/assets/blog-images/2024-3-15-isabelle-reconstruction/MetisTimeout1.png" alt="MetisTimeout1" class="center" width=80% />
</div>

## The solution: Proof certificates

SMT solvers are large and complex software systems that are constantly improved and extended. As any large software project they are known to have bugs even when applying best engineering practices.

<div align='center'>
<img src="/assets/blog-images/2024-3-15-isabelle-reconstruction/IsabelleAsksCvc5_2.svg" alt="IsabelleAsksCvc5_2" class="center"  width=80% />
</div>

One solution would be to verify the solver in Isabelle. This would be a massive effort that probably would require performance compromises. And since solvers are not static, each change would require expensive maintenance of the proofs.

Fortunately, there is a less expensive alternative. Instead of checking the whole solver once, we can check each result the solver outputs. In the case that a problem is *satisfiable* we require the solver to output a model that can be checked by evaluation. 

In Isabelle we are more interested in *unsatisfiable* results, since these show that the lemma is valid. In the *unsat* case, the solver outputs a *proof certificate*, a series of steps that explain how the solver concluded that the problem is `unsat`. Checking the steps should generally be easier than solving the problem. A tool that does this is called a proof checker. We will refer to the checking of `proof certificates` inside of Isabelle as replaying the proof or reconstructing the proof in the following. 

<div align='center'>
<img src="/assets/blog-images/2024-3-15-isabelle-reconstruction/IsabelleAsksCvc5_3.svg" alt="IsabelleAsksCvc5_3" class="center" width=80% />
</div>

It is not practical to have cvc5 print *proof certificates* using Isabelle's proof language. However, we can teach Isabelle to understand the solver's output. There are different formats for *proof certificates*. 

Isabelle already knows how to reconstruct proof steps in the [Alethe](https://verit.loria.fr/documentation/alethe-spec.pdf) proof format (see [here](https://arxiv.org/abs/1908.09480)). The SMT solver [veriT](https://verit.loria.fr/) outputs this format. It is complete for the theories of quantifier-free formulas with uninterpreted functions and linear arithmetic on real numbers and integers. It also supports quantifier problems. There is also an independent proof checker for the Alethe format called [Carcara](https://link.springer.com/chapter/10.1007/978-3-031-30823-9_19). Carcara is not currently formally verified.

### Outputting Proof Certificates in Alethe from cvc5 

We instructed cvc5 to output proofs in the Alethe format using its [modular proof infrastructure](https://link.springer.com/chapter/10.1007/978-3-031-10769-6_3). You can get Alethe proofs from cvc5 by using the flag `--proof-format-mode=alethe`. Note that support for Alethe proofs on the `main` branch of our cvc5 repo is still unstable and full support is available only on our proofs development branch [proof-new](https://github.com/cvc5/cvc5/tree/proof-new). We are running the last tests on this as we speak and it will soon be fully available in main as well. 

The transformation from internal cvc5 proofs to Alethe proofs is done in a post-processing step. Each proof step in the internal cvc5 proof is an instance of one of the proof rules of the [cvc5 calculus ](https://cvc5.github.io/docs/latest/proofs/proof_rules.html). The proof rule describes how the step was derived from its premises. For example, NOT_NOT_ELIM is a rule that allows the solver to reason that from a premise that is negated twice you can conclude the same statement but without the two negations.

<div align='center'>
<img src="/assets/blog-images/2024-3-15-isabelle-reconstruction/cvc5ProofRule.png" alt="cvc5ProofRule" class="center" width=70% />
</div>

Whenever a proof step with this rule appears in the internal cvc5 proof it has to be translated into one or more steps in the Alethe calculus. As an example, let's say that our premise is some assumption `(not (not (>= i 2048)))` and the conclusion of the currently translated step `F` is `(>= i 2048)`.

Luckily Alethe has a rule that is quite similar to the one in the cvc5 calculus, called `not_not`.  The way the rule is written down is a bit different from the way used in the cvc5 documentation. `not_not` has no premises and the conclusion `(cl (not (not (not phi))) phi)`. cl can be seen as or if it has more than two arguments, otherwise it does nothing.

<div align='center'>
<img src="/assets/blog-images/2024-3-15-isabelle-reconstruction/AletheProofRule.png" alt="AletheProofRule" class="center"/>
</div>

The translation we wrote is adding an additional step from the calculus: `resolution`. After that we reached the original conclusion and can now move on translating the other steps.

```
(assume a0 (not (not (>= i 2048))))
(step t1 (cl (not (not (not (>= i 2048)))) (>= i 2048)) :rule not_not :premises a0)
(step t2 (cl (>= i 2048)) :rule resultion :premises t1)

```
## The Reconstruction Cycle

Now we can put all the steps together. Inside of Isabelle we call sledgehammer on a goal. That generates an SMT-LIB problem that we give to cvc5. The proof certificate that we get receive from the solver is then parsed back in into Isabelle. The `smt` tactic checks every step of that proof and discharges the original goal.

<div align='center'>
<img src="/assets/blog-images/2024-3-15-isabelle-reconstruction/CENTAURRetreatSimp.svg" alt="CENTAURRetreatSimp" class="center"/>
</div>

In the next part of this series we will write about how the `smt` tactic works internally and what extensions we made to it. We will introduce our work on adding support for Alethe bit-vector proofs to Isabelle and speak about an important component of cvc5 proofs: rewrites. 

However, before we'll end this post, we want to present some of our first preliminary results that reuse the Alethe reconstruction infrastructure that we describe above.


## Isabelle as a Proof Checker and First Results

To be able to efficiently evaluate our work we have extended Isabelle to not just check proofs for problems that it generated itself. It can now parse an SMT-LIB problem and a proof and then check whether the assumptions from the proof occur in the problem and that every step in the proof is correct.

For this we introduced a new command called check_smt:

<div align='center'>
<img src="/assets/blog-images/2024-3-15-isabelle-reconstruction/checkSMT.png" alt="checkSMT" class="center" width=70% />
</div>

This command takes as an SMT-LIB problem and an Alethe proof for that problem as an input. It then reads in the problem: it generates types and terms for all definitions in the problem and creates an internal goal from the assertions. Then, it uses the same reconstruction process that it also uses for internal goals.

We have used this method to evaluate cvc5s performance on SMT-LIB XYZ benchmarks

```
|                             | cvc5        | verit      |
| ----------------------------| ----------- |----------- |
| nr benchmarks solved        |             |            |
| nr benchmarks reconstructed |             |            |
```

Are you intrigued about the differences between cvc5 with rewrites and without? Keep your eyes open for part 2 of this series on Isabelle and cvc5.

#### [Hanna Lachnitt](https://lachnitt.github.io/) is a PhD student advised by Clark Barrett in the Stanford Center for Automated Reasoning ([Centaur](https://centaur.stanford.edu/)) Lab. Her research is focused on SMT Proofs.
