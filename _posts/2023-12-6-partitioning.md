---
layout: blog-post
categories: blog
excerpt_separator: <!--more-->
title: "Partitioning Strategies for Distributed SMT Solving"
author: Amalee Wilson
date: 2023-12-6
---

Partitioning is a divide-and-conquer approach where a difficult problem is split into hopefully easier subproblems that can be solved in parallel. This strategy is notoriously difficult to get right with SMT problems. We found that while it’s no panacea, partitioning can be used to diversify solving and reliably improve performance in a portfolio. 
<!--more-->


Many users of SMT solvers find that the solver’s performance is the main bottleneck in their application, yet most SMT solvers remain single-threaded. We sought to explore a divide-and-conquer strategy for accelerating SMT solving. Six main strategies were explored, using three different sources of atoms for the partitions and two different types of partitioning. More details about these partitioning strategies and the various parameters can be found in the [paper that we recently published at FMCAD 2023](https://repositum.tuwien.at/bitstream/20.500.12708/188827/1/Wilson-2023-Partitioning%20Strategies%20for%20Distributed%20SMT%20Solving-vor.pdf). 
Many of these partitioning strategies work well for the QF_LRA, QF_LIA, QF_IDL, QF_UF, and QF_RDL challenge benchmarks used for the paper. However, the main contribution was discovering that interesting new portfolio techinques could be applied using these different strategies. Portfolio solving is an approach in which multiple solvers (or different configurations of a solver), attempt to solve the same (or perturbed but equivalent) SMT problem in parallel. 

![Alt Text](/assets/blog-images/hybrid-portfolio.png)

The best portfolio technique that we created is the hybrid graduated partitioning portfolio. 
We call this approach "hybrid" because it uses both partitioning strategies and a more traditional portfolio approach of scrambling (where the copies of the original problem are semantically equivalent but mutated). The "graduated" part of the name refers to how one or more partitioning strategies are used to create 2, 4, 8, and so on independent sets of partitions that are all solved in parallel. Imagine that there are a total of 24 processors available. 12 of those can be solving 12 different scrambled versions of the problem. 2 of them can be solving 2 partitions created with partitioning strategy A, and another 4 are solving 4 different partitions created with partitioning strategy A. The remaining 6 processors are solving one set of 2 and one set of 4 partitions created with partitioning strategy B. 


This interesting portfolio was motivated by the observation that each aspect introduces diversity into the portfolio. When using a single partitioning strategy, a graduated portfolio can produce better results than the same number of partitions made in a single step: using 30 cores to solve four sets of partitions (2, 4, 8, and 16) in parallel typically outperforms using 32 cores to solve one set of 32 partitions. Additionally, different partitioning strategies introduce diversity, and using scrambling seems to impart a different kind of diversity on the portfolio. More details can be found in the paper. 

If you're interested in trying out some of our partitioning strategies, they can all be found in cvc5's main branch on GitHub! Here's how you use it: 


For time-based cube type partitions: 
```
cvc5 --partition-when=tlimit --compute-partitions=8 --partition-start-time=3 --partition-strategy=decision-cube
```
8 can be replaced with the desired number of partitions (must be a power of 2 for cube type partitions),
3 can be replaced with the desired number of seconds to wait until creating partitions (3 is empirically a good choice here),
and decision-cube can be replaced with any cube type partition strategy: decision-cube, lemma-cube, or heap-cube. Additional documentation for different partitioning parameters can be found under the parallel options documentation. 