---
layout: awards

event: SMT-COMP 2023
event_url: https://smt-comp.github.io/2023

version:
binaries:
- name: Single Query, Unsat Core, and Model Validation Tracks
  binary: https://www.starexec.org/starexec/secure/details/solver.jsp?id=44737
- name: Incremental Track
  binary: https://www.starexec.org/starexec/secure/details/solver.jsp?id=44738

sysdesc-title: cvc5 at the SMT Competition 2023
sysdesc-url: /papers/2023/smt-comp-2023.pdf

entered:

- track: single-query
  name: Single Query Track
  divisions: Arith, Bitvec, Equality+LinearArith, Equality+MachineArith,
             Equality+NonLinearArith, Equality, FPArith, QF_Bitvec,
             QF_Datatypes, QF_Equality+Bitvec, QF_Equality+LinearArith,
             QF_Equality+NonLinearArith, QF_Equality, QF_FPArith,
             QF_LinearIntArith, QF_LinearRealArith, QF_NonLinearIntArith,
             QF_NonLinearRealArith, QF_Strings

- track: incremental
  name: Incremental Track
  divisions: Arith, Bitvec, Equality, Equality+LinearArith,
             Equality+MachineArith, Equality+NonLinearArith, FPArith, QF_Bitvec,
             QF_Equality+Bitvec+Arith, QF_Equality+Bitvec, QF_Equality,
             QF_Equality+LinearArith, QF_Equality+NonLinearArith, QF_FPArith,
             QF_LinearIntArith, QF_LinearRealArith, QF_NonLinearIntArith

- track: unsat-core
  name: Unsat Core Track
  divisions: Arith, Bitvec, Equality+LinearArith, Equality+MachineArith,
             Equality+NonLinearArith, Equality, FPArith, QF_Bitvec,
             QF_Datatypes, QF_Equality+Bitvec, QF_Equality+LinearArith,
             QF_Equality+NonLinearArith, QF_Equality, QF_FPArith,
             QF_LinearIntArith, QF_LinearRealArith

- track: model-validation
  name: Model Validation Track
  divisions: QF_ADT+BitVec, QF_ADT+LinArith, QF_Array+Bitvec+LinArith,
             QF_Bitvec, QF_Datatypes, QF_Equality+Bitvec,
             QF_Equality+LinearArith, QF_Equality, QF_Equality+NonLinearArith,
             QF_FPArith, QF_LinearIntArith, QF_LinearRealArith,
             QF_NonLinearIntArith, QF_NonLinearRealArith


tracks:

- track: single-query
  name: Single Query Track
  medals:
  - division: Arith
    awards: sequential, parallel, unsat
    place: 1
  - division: Bitvec
    awards: sequential, parallel, unsat
    place: 1
  - division: Equality+LinearArith
    place: 1
  - division: Equality+MachineArith
    place: 1
  - division: Equality+NonLinearArith
    place: 1
  - division: Equality
    awards: sequential, parallel, sat, unsat
    place: 1
  - division: QF_Datatypes
    awards: sequential, parallel, sat, unsat
    place: 1
  - division: QF_Equality+NonLinearArith
    awards: sequential, parallel, unsat, 24s
    place: 1
  - division: QF_LinearIntArith
    awards: unsat
    place: 1
  - division: QF_LinearRealArith
    awards: unsat
    place: 1
  - division: QF_NonLinearRealArith
    awards: unsat, 24s
    place: 1
  - division: QF_Strings
    awards: sequential, parallel, sat, unsat
    place: 1

- track: incremental
  name: Incremental Track
  medals:
  - division: Arith
    place: 1
  - division: Bitvec
    place: 1
  - division: Equality
    place: 1
  - division: Equality+LinearArith
    place: 1
  - division: Equality+NonLinearArith
    place: 1
  - division: QF_Equality+Bitvec+Arith
    place: 1
  - division: QF_Equality
    place: 1
  - division: QF_Equality+NonLinearArith
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
  - division: QF_Datatypes
    awards: sequential
    place: 1
  - division: QF_Equality+NonLinearArith
    place: 1
  - division: QF_FPArith
    place: 1

overall:

- award: biggest-lead
  name: Biggest Lead
  tracks:
  - track: single-query
    name: Single Query Track
    awards: sequential, parallel, sat, unsat
    place: 1
  - track: single-query
    name: Single Query Track
    awards: 24s
    place: 2
  - track: incremental
    name: Incremental Track
    place: 3
  - track: unsat-core
    name: Unsat Core Track
    place: 1

- award: largest-contribution
  name: Largest Contribution
  tracks:
  - track: single-query
    name: Single Query Track
    place: 1
  - track: incremental
    name: Incremental Track
    place: 1
  - track: unsat-core
    name: Unsat Core Track
    place: 1

---
