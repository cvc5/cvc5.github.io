---
layout: awards

event: SMT-COMP 2022
event_url: https://smt-comp.github.io/2022

version:
binaries:
- name: Single Query, Unsat Core, and Model Validation Tracks
  binary: https://www.starexec.org/starexec/secure/details/solver.jsp?id=39117
- name: Incremental Track
  binary: https://www.starexec.org/starexec/secure/details/solver.jsp?id=39114

sysdesc-title: cvc5 at the SMT Competition 2022
sysdesc-url: /papers/2022/smt-comp-2022.pdf

entered:

- track: single-query
  name: Single Query Track
  divisions: Arith, Bitvec, Equality, Equality+LinearArith,
             Equality+MachineArith, Equality+NonLinearArith, FPArith, QF_Bitvec,
             QF_Datatypes, QF_Equality, QF_Equality+Bitvec,
             QF_Equality+Bitvec+Arith, QF_Equality+LinearArith,
             QF_Equality+NonLinearArith, QF_FPArith,
             QF_LinearIntArith, QF_LinearRealArith, QF_NonLinearIntArith,
             QF_NonLinearRealArith, QF_Strings

- track: incremental
  name: Incremental Track
  divisions: Arith, Bitvec, Equality, Equality+LinearArith,
             Equality+MachineArith, Equality+NonLinearArith, FPArith, QF_Bitvec,
             QF_Equality, QF_Equality+Bitvec,
             QF_Equality+Bitvec+Arith, QF_Equality+LinearArith,
             QF_Equality+NonLinearArith, QF_FPArith,
             QF_LinearIntArith, QF_LinearRealArith, QF_NonLinearIntArith

- track: unsat-core
  name: Unsat Core Track
  divisions: Arith, Bitvec, Equality, Equality+LinearArith,
             Equality+MachineArith, Equality+NonLinearArith, FPArith, QF_Bitvec,
             QF_Datatypes, QF_Equality, QF_Equality+Bitvec,
             QF_Equality+LinearArith,
             QF_Equality+NonLinearArith, QF_FPArith,
             QF_LinearIntArith, QF_LinearRealArith, QF_NonLinearIntArith,
             QF_NonLinearRealArith, QF_Strings

- track: model-validation
  name: Model Validation Track
  divisions: QF_Bitvec, QF_Equality, QF_Equality+Bitvec,
             QF_Equality+LinearArith, QF_FPArith, QF_LinearIntArith,
             QF_LinearRealArith


tracks:

- track: single-query
  name: Single Query Track
  medals:
  - division: Arith
    awards: sequential, parallel, unsat
    place: 1
  - division: Bitvec
    awards: sequential, parallel, sat, unsat
    place: 1
  - division: Equality+LinearArith
    place: 1
  - division: Equality+MachineArith
    place: 1
  - division: Equality+NonLinearArith
    awards: unsat
    place: 1
  - division: Equality
    awards: sequential, parallel, sat, unsat
    place: 1
  - division: QF_Datatypes
    awards: sequential, parallel, sat, unsat
    place: 1
  - division: QF_Equality+NonLinearArith
    place: 1
  - division: QF_LinearIntArith
    awards: unsat
    place: 1
  - division: QF_LinearRealArith
    awards: unsat
    place: 1
  - division: QF_NonLinearIntArith
    awards: sequential, parallel, sat
    place: 1
  - division: QF_NonLinearRealArith
    awards: sequential, parallel, unsat, 24s
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
  - division: Equality+NonLinearArith
    place: 1
  - division: Equality
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
    awards: sequential
    place: 1
  - divisions: QF_Datatypes
    place: 1

overall:

- award: biggest-lead
  name: Biggest Lead
  tracks:
  - track: single-query
    name: Single Query Track
    place: 1
  - track: unsat-core
    name: Unsat Core Track
    place: 1
  - track: incremental
    name: Incremental Track
    place: 3

- award: largest-contribution
  name: Largest Contribution
  tracks:
  - track: incremental
    name: Incremental Track
    place: 1
  - track: single-query
    name: Single Query Track
    awards: sequential, parallel, sat, unsat
    place: 1
  - track: unsat-core
    name: Unsat Core Track
    place: 1

- name: FLoC'22 Olympic Games
  url: https://www.floc2022.org/floc-olympic-games
  medals:
  - medal: 3 gold medals

img: /img/floc22-smt.jpg

---
