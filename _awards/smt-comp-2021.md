---
layout: awards

event: SMT-COMP 2021
event_url: https://smt-comp.github.io/2021

version:
binaries:
- track: single-query
  name: Single Query Track
  binary: https://www.starexec.org/starexec/secure/details/solver.jsp?id=33471
- track: incremental
  name: Incremental Track
  binary: https://www.starexec.org/starexec/secure/details/solver.jsp?id=33472
- track: unsat-core
  name: Unsat Core Track
  binary: https://www.starexec.org/starexec/secure/details/solver.jsp?id=33474
- track: model-validation
  name: Model Validation Track
  binary: https://www.starexec.org/starexec/secure/details/solver.jsp?id=33473
sysdesc-title: cvc5 at the SMT Competition 2021
sysdesc-url: /papers/2021/smt-comp-2021.pdf

entered:

- track: single-query
  name: Single Query Track
  divisions: Arith, Bitvec, Equality+LinearArith, Equality+MachineArith,
             Equality+NonLinearArith, Equality, FPArith, QF_Bitvec,
             QF_Equality+Bitvec, QF_Equality+LinearArith,
             QF_Equality+NonLinearArith, QF_Equality, QF_FPArith,
             QF_LinearIntArith, QF_LinearRealArith, QF_NonLinearIntArith,
             QF_NonLinearRealArith, QF_Strings

- track: incremental
  name: Incremental Track
  divisions: Arith, Bitvec, Equality+LinearArith, Equality+NonLinearArith,
             Equality, FPArith, QF_Bitvec, QF_Equality+Bitvec,
             QF_Equality+LinearArith, QF_Equality+NonLinearArith, QF_Equality,
             QF_FPArith, QF_LinearIntArith, QF_LinearRealArith,
             QF_NonLinearIntArith

- track: unsat-core
  name: Unsat Core Track
  divisions: Arith, Bitvec, Equality+LinearArith, Equality+MachineArith,
             Equality+NonLinearArith, Equality, FPArith, QF_Bitvec,
             QF_Equality+Bitvec, QF_Equality+LinearArith,
             QF_Equality+NonLinearArith, QF_Equality, QF_FPArith,
             QF_LinearIntArith, QF_LinearRealArith, QF_NonLinearIntArith,
             QF_NonLinearRealArith

- track: model-validation
  name: Model Validation Track
  divisions: QF_Bitvec, QF_Equality+Bitvec, QF_Equality+LinearArith,
             QF_Equality, QF_LinearIntArith, QF_LinearRealArith


tracks:

- track: single-query
  name: Single Query Track
  medals:
  - division: Arith
    awards: sequential, parallel, sat, 24s
    place: 1
  - division: Bitvec
    place: 1
  - division: Equality+LinearArith
    place: 1
  - division: Equality+MachineArith
    place: 1
  - division: Equality+NonLinearArith
    awards: unsat
    place: 1
  - division: Equality
    awards: unsat
    place: 1
  - division: FPArith
    place: 1
  - division: QF_Equality+LinearArith
    awards: unsat
    place: 1
  - division: QF_Equality+NonLinearArith
    place: 1
  - division: QF_Equality
    awards: sequential, parallel, sat, unsat
    place: 1
  - division: QF_FPArith
    place: 1
  - division: QF_LinearIntArith
    awards: sequential, parallel, sat, unsat
    place: 1
  - division: QF_LinearRealArith
    awards: unsat
    place: 1
  - division: QF_NonLinearIntArith
    awards: sequential, parallel, sat
    place: 1
  - division: QF_NonLinearRealArith
    place: 1
  - division: QF_Strings
    place: 1

- track: incremental
  name: Incremental Track
  medals:
  - division: Arith
    place: 1
  - division: Bitvec
    place: 1
  - division: Equality+LinearArith
    place: 1
  - division: Equality
    place: 1
  - division: FPArith
    place: 1
  - division: QF_Equality+LinearArith
    place: 1
  - division: QF_Equality
    place: 1

- track: model-validation
  name: Model Validation Track
  medals:
  - division: QF_LinearIntArith
    place: 1

- track: unsat-core
  name: Unsat Core Track
  medals:
  - division: Arith
    place: 1
  - division: Bitvec
    place: 1
  - division: Equality+LinearArith
    place: 1
  - division: Equality+MachineArith
    place: 1
  - division: Equality+NonLinearArith
    place: 1
  - division: Equality
    place: 1
  - division: FPArith
    place: 1
  - division: QF_Equality+NonLinearArith
    place: 1
  - division: QF_Equality
    place: 1
  - division: QF_LinearIntArith
    place: 1
  - division: QF_NonLinearIntArith
    place: 1
  - division: QF_NonLinearRealArith
    place: 1

overall:

- award: biggest-lead
  name: Biggest Lead
  tracks:
  - track: incremental
    name: Incremental Track
    place: 1
  - track: model-validation
    name: Model Validation Track
    place: 1
  - track: single-query
    name: Single Query Track
    place: 1
  - track: unsat-core
    name: Unsat Core Track
    place: 1

- award: largest-contribution
  name: Largest Contribution
  tracks:
  - track: incremental
    name: Incremental Track
    place: 1
  - track: model-validation
    name: Model Validation Track
    place: 1
  - track: single-query
    name: Single Query Track
    awards: sat, unsat
    place: 1
  - track: unsat-core
    name: Unsat Core Track
    place: 1
  - track: single-query
    name: Single Query Track
    awards: sequential, 24s
    place: 2
  - track: single-query
    name: Single Query Track
    awards: parallel
    place: 3
---
