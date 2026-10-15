---
layout: blog-post
categories: blog
excerpt_separator: <!--more-->
title: "Reconstructing cvc5 Proofs in Isabelle/HOL - Part 2: Verifying String Rewrite Rules"
author: Hanna Lachnitt
date: 2026-10-14
---

In [part 1](https://cvc5.github.io/blog/2024/03/15/isabelle-reconstruction.html) of this series, we showed how we use proof certificates to improve cvc5's communication with the interactive theorem prover Isabelle. A proof certificate is a series of steps that justifies that the input is *unsatisfiable*. Because Isabelle negates the proof goal before passing it to cvc5, the certificate is a proof by contradiction that shows that the original goal is valid. Common steps in such certificates are term rewrites, which often simplify an expression or eliminate operators that can be expressed in terms of other operators.

<!--more-->

In this blog post, we describe how term rewrite rules can be verified in Isabelle/HOL. The resulting lemmas can subsequently be used automatically when reconstructing proof certificates. While we verified rewrite rules for all theories we support in Isabelle's smt method (see our [paper](https://link.springer.com/chapter/10.1007/978-3-032-32526-6_9)), we use the theory of strings to illustrate how this process works and what we learned along the way.

## Why strings matter for verification

Mishandling strings is a common source of bugs, and because strings are often used in programs that handle sensitive data, these bugs can lead to serious security vulnerabilities. Cross-site scripting and SQL injection are just two common examples of attacks made possible by string-related errors. Thankfully, SMT solvers such as cvc5 can help catch these types of bugs.

Strings also play a key role in many access control systems used to safeguard cloud resources. Amazon Web Services (AWS), for example, allows users to specify access policies for their resources [using a domain-specific language](https://docs.aws.amazon.com/AmazonS3/latest/userguide/access-policy-language-overview.html). In this language, a policy consists of a series of Allow and Deny statements that control who can perform which actions on which resources, and under which conditions. The statements often contain regular expressions.

For instance, suppose an instructor teaches two computer science classes, CS 123 and CS 321, and uses AWS to give her students access to course materials. All students should have access to the homework for the class they are in. To prevent cheating, students must not have access to any exams. CS 321 builds on the content of CS 123, so the instructor wants the students in CS 321 to be able to look at lecture slides and homework from CS 123 to review. To meet these goals, the instructor writes the following access policy (presented in a simplified version of the AWS policy language).

```
{(Allow,
Who : All-Students,
Action : ReadFile,
Resource : "my-bucket/$course_name/*",
),
(Deny,
Who : All-Students,
Action : *,
Resource : "my-bucket/$course_name/exams/*",
),
(Allow,
Who : CS321-Students,
Action : ReadFile,
Resource : "my-bucket/cs123/*",
)}
```

Assume the variable `$course_name` gets set to `cs123` or `cs321` depending on which course a student is enrolled in. At first glance, this policy looks like it enforces the instructor's intent, but it actually gives some students access to exams they should not have. The second `Allow` statement gives students in CS 321 access to all CS 123 materials, including exams, but the `Deny` statement only prevents students from having access to the exams for their *own* class.

Since the consequences of policies can be difficult to understand, AWS created [Zelkova](https://aws.amazon.com/blogs/security/protect-sensitive-data-in-the-cloud-with-automated-reasoning-zelkova/), a tool that translates policies into logical constraints and checks whether a policy allows unintended access by querying SMT solvers. cvc5's efficient decision procedures for reasoning about strings and regular expressions make it a good match for verification tasks involving strings.

## String term rewrites in cvc5's proof certificates

Modern SMT solvers rely on hundreds of different kinds of term rewrites. To avoid slowing down solving, cvc5 follows a [modular approach](https://link.springer.com/chapter/10.1007/978-3-031-10769-6_3) when it generates proof certificates. During its solving phase, it does not record which term rewrite steps it applies. Instead, the resulting coarse-grained proof steps are elaborated into finer-grained steps during a post-processing phase.

In the following example, proof step `t1` is not elaborated yet and is not justified by a helpful proof rule but by the `hole` rule which indicates a gap in the proof. The step postulates that taking a substring of the empty string "" is the empty string itself.

```
(step t1 (cl (= (str.substr "" x y) "")) :rule hole :args ("untranslated rewrite"))
```

Note: `cl` corresponds to the identity if it is applied to only one argument and to `or` if it has more than one argument.

After elaboration, `t1` has been split into two steps. First, cvc5 shows that the empty string has length 0 in `t1'` and then it uses that fact to argue that any substring must therefore be empty in step `t2'`.

```
(step t1' (cl (= (str.len "") 0)) :rule evaluate)
(step t2' (cl (= (str.substr "" x y) "")) :rule rare_rewrite :premises (t1') :args ("str-substr-empty-str" "" x y))
```

Instead of relying on a hard-coded set of rules, cvc5 can read rewrite rules from a database. These rules are written in a domain-specific language called [RARE](https://link.springer.com/chapter/10.1007/978-3-031-57246-3_17#Sec8). This language is powerful enough to express cvc5's term rewriting steps while remaining easy to use. In the example above, `t2'` is justified by the RARE rewrite rule called `str-substr-empty-str`.

At a high level, you can think of a RARE rule as having a name, a parameter list, a match expression, and a target expression. If an expression matches the rule's match expression, the expression is replaced with the target expression. Some rules have conditions that have to be met for their rewrites to be applied, and some rules get applied repeatedly until the expression does not match the rule's match expression anymore.

### A first example: string operators

Consider the `str-contains-lt-len` rule below. An expression that matches `(str.contains x y)` is rewritten to the target expression `false` whenever the condition `(> (str.len y) (str.len x))` holds.

<img
  width="100%"
  src="/assets/blog-images/2026-10-14-isabelle-rewrite-string-verification/str-contains-lt-len-labeled.png"/>

The intuition behind this rule is that if `y` is longer than `x`, there is no way `x` can contain `y`, so the predicate `(str.contains x y)` can be rewritten to `false`, as in the following example.

<img
  width="50%"
  src="/assets/blog-images/2026-10-14-isabelle-rewrite-string-verification/too_long.png"/>

Clearly, the string `cat` cannot contain the string `category`, and we do not even have to examine the content of the strings to conclude that, but only their lengths.


### A second example: regular expressions

The rule `str-in-re-contains` connects regular expressions of a specific form to string containment.

```
(define-rule str-in-re-contains ((t String) (s String))
  (str.in_re t (re.++ (re.* re.allchar) (str.to_re s) (re.* re.allchar)))
  (str.contains t s))
```
Here, `(str.in_re t r)` tests whether the string `t` is in the language of the regular expression `r`. `re.allchar` matches any single character, `re.*` is the Kleene star (zero or more repetitions), `str.to_re s` matches exactly the string `s`, and `re.++` concatenates regular expressions. So the membership predicate on the second line tests if $\texttt{t} \in \texttt{UC}^\star \texttt{\{s\}} \texttt{UC}^\star$, where $\texttt{UC}$ is the set of Unicode characters. The following diagram illustrates the strings represented by this regular expression.

<img
  width="100%"
  src="/assets/blog-images/2026-10-14-isabelle-rewrite-string-verification/re-contain.png"/>
  

What the rule is expressing is that a string $\texttt{t}$ contains $\texttt{s}$ precisely when $\texttt{t}$ is generated by sandwiching $\texttt{s}$ between two arbitrary sequences of Unicode characters. So the regex membership test that represents this sandwiching can be replaced by a containment test.


## Translating RARE rules into Isabelle

We used [IsaRARE](https://link.springer.com/chapter/10.1007/978-3-031-57246-3_17) to translate the rewrite rules from RARE into lemmas in the interactive theorem prover Isabelle. IsaRARE reuses the SMT-LIB parser utilities Isabelle needs for its `smt` method. While most SMT-LIB theories are already supported, for strings we had to extend the parser with the correspondences between SMT-LIB operators and Isabelle operators.

<img
  width="100%"
  src="/assets/blog-images/2026-10-14-isabelle-rewrite-string-verification/pipeline.png"/>

### Translating string terms

Until now, we have glossed over how expressions in the RARE rules have to be written and how the solver interprets them. Syntactically, RARE terms are based on the SMT-LIB language, the standard input format for SMT solvers. Semantically, cvc5 follows the standard theories SMT-LIB provides, including the [theory of strings](https://smt-lib.org/theories-UnicodeStrings.shtml). In it, as you can see here, strings are defined as lists of Unicode characters.

<img
  width="100%"
  src="/assets/blog-images/2026-10-14-isabelle-rewrite-string-verification/smtlib_string_theory.png"/>
  
The strings theory also defines functions corresponding to various string operations you would find in programming languages' standard libraries. For instance, the theory includes concatenation, substring, length, containment, and replacement. Furthermore, it provides predefined operators for regular expressions. SMT-LIB regular expressions can function as patterns for search and replacement like the regular expressions in major programming languages, but they are formally defined as sets of strings as in formal language theory.

Isabelle's standard library for strings is not compatible with SMT-LIB since Isabelle's strings can only contain ASCII characters as opposed to the more general Unicode. Fortunately, [Lotz et al](https://link.springer.com/chapter/10.1007/978-3-031-40247-0_15#Sec3). developed a formalization of the SMT-LIB theory of strings that we were able to reuse. This formalization defines its own string type as lists of integers in the Unicode range. It supplies an Isabelle implementation of almost every function in the SMT-LIB theory of strings, which is very helpful for translation and verification.

For example, Lotz et al. defined the Kleene star `r*` as the union of the regular languages `L_i` consisting of `i` concatenations of `r`.

<img
  width="75%"
  src="/assets/blog-images/2026-10-14-isabelle-rewrite-string-verification/re_star_isabelle_def.png"/>

Compare this to the SMT-LIB definition of the operator, which uses an existential quantifier.

<img
  width="100%"
  src="/assets/blog-images/2026-10-14-isabelle-rewrite-string-verification/re_star_smtlib.png"/>

The way `star` is defined makes it easier to prove statements about it, but it is not obvious that it models the SMT-LIB definition perfectly. Therefore, Lotz et al. proved the following correctness lemma to show the correspondence.

<img
  width="100%"
  src="/assets/blog-images/2026-10-14-isabelle-rewrite-string-verification/re_star_isabelle.png"/>
  
The library also contains an alternative datatype representation for regular expressions. We supplemented this work with our own Isabelle formalizations of a few replacement operators that were not included.

### Translating rules: IsaRARE

Once terms can be translated, IsaRARE can convert the complete rule into a lemma. For instance, this is the RARE rule `str-contains-lt-len` that we have seen before:

    (define-cond-rule str-contains-lt-len ((x String) (y String))
      (> (str.len y) (str.len x))
      (str.contains x y)
      false)

The condition `(> (str.len y) (str.len x))` is now the antecedent of an implication. The match and the target are set equal.

<img
  width="80%"
  src="/assets/blog-images/2026-10-14-isabelle-rewrite-string-verification/str-contains-lt-len-screenshot.png"/>

After translation, if the lemma can be proven in Isabelle, the corresponding proof rule is considered sound, modulo having to trust the translation into Isabelle, which we tested with a large number of benchmarks.


## Verifying the RARE rules

Unsound rewrite rules can result in incomplete or erroneous proof certificates, or, in the worst case, reflect unsoundness in the solver code they are modeled on. We therefore set out to verify all string and regular expression rewrite rules by finding proofs for the generated lemmas. Isabelle uses a small trusted kernel to check that proofs are correct, leaving us with high assurance of the soundness of the rules. 

We proved all translated lemmas in Isabelle, thus showing the soundness of cvc5's string rewrite rules. Many lemmas could be proven automatically using Isabelle's powerful proof automation tool Sledgehammer. The rest required more human effort to prove. Finally, in a few rare cases, we struggled heavily to prove a lemma and realized that the issue was that the corresponding rule was buggy. Thankfully, none of the bugs we found originated from unsound solver code. All buggy rules were repaired and proven correct in Isabelle afterwards.

### Example of an unsound rule

The following rule used to be in the main branch of cvc5:

```
(define-cond-rule str-in-re-no-prefix ((s1 String) (s2 String) (r RegLan))
  (not (str.in_re s1 (re.++ r (re.* re.allchar))))
  (str.in_re (str.++ s1 s2) r)
  false)
```

In natural language, this rule claims that if none of the strings in a regular language `r` is a prefix of `s1`, then `s1` is not a prefix of any string in `r`.  The Isabelle lemma corresponding to this rule is the following:

<img
  width="80%"
  src="/assets/blog-images/2026-10-14-isabelle-rewrite-string-verification/str-in-re-no-prefix-screenshot.png"/>

This rule is not sound, and Isabelle was able to generate a counterexample to it. A simpler counterexample illustrating the same problem is `s1 = "logic"`, `r = {"logician"}`, and `s2 = "ian"`. No string in `r` is a prefix of `s1`, so the rule's condition holds. The rule then says that we should be able to replace the regular expression membership test result with false, but that is incorrect because `(str.++ s1 s2)` is `"logician"`, which is in `r`.

We found six other rules that were unsound. One of these made the same error with suffixes instead of prefixes. Two rules had bugs in the operators' error cases, e.g., if an index is negative some operators specify the result to be -1. Another rule involved a type error. One was incorrect in an edge case and one had a typo in it. All of these rules were either removed from cvc5 or corrected after we discovered the errors. Fortunately, none of these rules caused or reflected soundness problems in cvc5's sat/unsat results.

### Reporting specification errors

We found some ambiguities and typos in SMT-LIB's definitions as we formalized the operators that were not in Lotz et al.'s formalization of SMT-LIB's theory of strings as well as some operators specific to cvc5. The definition of SMT-LIB's `str.replace_re_all` was ambiguous for certain cases. Furthermore, the cases in the SMT-LIB definition of `str.replace_re` were not exhaustive. Moreover, the documentation for cvc5's nonstandard `str.indexof_re` operator did not match what cvc5 actually did with that operator. 

We reported each of these errors to the maintainers of the relevant documentation, and the cvc5 documentation has been corrected.

## Results and conclusion

We proved all **180** rules that cvc5 uses for strings and regular expressions sound. If a rule was phrased on sequences (which are more general than strings), we instantiated it with strings. We use the same process to verify rewrite rules for other theories.

While Isabelle's `smt` method does not yet send string goals to cvc5, using the lemmas for proof reconstruction is straightforward. Let's return to our earlier example:

```
(step t1' (cl (= (str.len "") 0)) :rule evaluate)
(step t2' (cl (= (str.substr "" x y) "")) :rule rare_rewrite :premises (t1') :args ("str-substr-empty-str" "" x y))
```

The lemma for the rule `str-substr-empty-str` is:

<img
  width="70%"
  src="/assets/blog-images/2026-10-14-isabelle-rewrite-string-verification/str_substr_empty_str.png"/>
  
During the reconstruction, we instantiate the lemma with the arguments of the step: the lemma's `x` becomes `""`, its `n` becomes the step's `x`, and its `m` becomes the step's `y`. This gives us `str_len "" = 0 ⟶ str_substr "" x y = ""`. Its premise `str_len "" = 0` is exactly what we proved in step `t1'`, so we can discharge it and obtain `t2'`.

We hope you had fun on this little journey into verifying string rewrite rules. If you want to read more about cvc5 and Isabelle, our [ITP 2025 paper](https://drops.dagstuhl.de/storage/00lipics/lipics-vol352-itp2025/LIPIcs.ITP.2025.26/LIPIcs.ITP.2025.26.pdf) is a good place to start.


#### [Hanna Lachnitt](https://lachnitt.github.io/) is a PhD student advised by Clark Barrett in the Stanford Center for Automated Reasoning ([Centaur](https://centaur.stanford.edu/)) Lab. Her PhD work is focused on SMT proof certificates and their use in Interactive theorem provers.
[Jibiana Jakpor](https://jjakpor.github.io/) finished her undergraduate studies at Stanford in 2026 and is now a PhD student advised by [Adam Chlipala at MIT CSAIL](https://adam.chlipala.net/). Her PhD work is focused on designing efficient proof automation.
