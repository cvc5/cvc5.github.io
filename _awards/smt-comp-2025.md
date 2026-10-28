---
layout: awards

event: SMT-COMP 2025
event_url: https://smt-comp.github.io/2025
division_url_sep: _

version:
binaries:
- name: All Tracks
  binary: https://zenodo.org/records/15760304/files/cvc5-default.zip

sysdesc-title: cvc5 at the SMT Competition 2025
sysdesc-url: https://zenodo.org/records/15760304/files/cvc5.pdf

entered:

- track: single-query
  name: Single Query Track
  divisions: Arith, Bitvec, Equality, Equality_LinearArith,
             Equality_MachineArith, Equality_NonLinearArith, FPArith, QF_Bitvec,
             QF_Datatypes, QF_Equality, QF_Equality_Bitvec,
             QF_Equality_LinearArith, QF_Equality_NonLinearArith, QF_FPArith,
             QF_LinearIntArith, QF_LinearRealArith, QF_NonLinearIntArith,
             QF_NonLinearRealArith, QF_Strings

- track: incremental
  name: Incremental Track
  divisions: Arith, Bitvec, Equality, Equality_LinearArith,
             Equality_MachineArith, Equality_NonLinearArith, FPArith, QF_Bitvec,
             QF_Equality, QF_Equality_Bitvec, QF_Equality_Bitvec_Arith,
             QF_Equality_LinearArith, QF_Equality_NonLinearArith, QF_FPArith,
             QF_LinearIntArith, QF_LinearRealArith, QF_NonLinearIntArith

- track: unsat-core
  name: Unsat Core Track
  divisions: Arith, Bitvec, Equality, Equality_LinearArith,
             Equality_MachineArith, Equality_NonLinearArith, FPArith, QF_Bitvec,
             QF_Datatypes, QF_Equality, QF_Equality_Bitvec,
             QF_Equality_LinearArith, QF_Equality_NonLinearArith, QF_FPArith,
             QF_LinearIntArith, QF_LinearRealArith, QF_NonLinearIntArith,
             QF_NonLinearRealArith

- track: model-validation
  name: Model Validation Track
  divisions: QF_ADT_BitVec, QF_ADT_LinArith, QF_Bitvec, QF_Datatypes,
             QF_Equality, QF_Equality_Bitvec, QF_Equality_LinearArith,
             QF_Equality_NonLinearArith, QF_FPArith, QF_LinearIntArith,
             QF_LinearRealArith, QF_NonLinearIntArith, QF_NonLinearRealArith


tracks:

- track: single-query
  name: Single Query Track
  medals:
  - division: Bitvec
    awards: sequential, parallel, unsat
    place: 1
  - division: Equality
    place: 1
  - division: Equality_LinearArith
    place: 1
  - division: Equality_MachineArith
    place: 1
  - division: Equality_NonLinearArith
    place: 1
  - division: QF_Datatypes
    awards: sequential, parallel, sat, unsat
    place: 1
  - division: QF_Equality_NonLinearArith
    awards: unsat
    place: 1

- track: incremental
  name: Incremental Track
  medals:
  - division: Arith
    awards: parallel
    place: 1
  - division: Bitvec
    place: 1
  - division: Equality
    place: 1
  - division: Equality_LinearArith
    awards: parallel
    place: 1
  - division: Equality_MachineArith
    awards: 24s
    place: 1
  - division: Equality_NonLinearArith
    place: 1
  - division: QF_Equality_NonLinearArith
    awards: 24s
    place: 1

- track: unsat-core
  name: Unsat Core Track
  medals:
  - division: Arith
    place: 1
  - division: Bitvec
    place: 1
  - division: Equality
    place: 1
  - division: Equality_LinearArith
    place: 1
  - division: Equality_MachineArith
    place: 1
  - division: Equality_NonLinearArith
    place: 1
  - division: QF_Datatypes
    awards: sequential, parallel, unsat
    place: 1
  - division: QF_Equality_NonLinearArith
    awards: sequential, parallel, unsat
    place: 1

- track: model-validation
  name: Model Validation Track
  medals:
  - division: QF_Equality_NonLinearArith
    place: 1
  - division: QF_FPArith
    awards: sequential, parallel, sat
    place: 1

overall:

- award: best-overall
  name: Best Overall
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
  - track: model-validation
    name: Model Validation Track
    place: 1

- award: biggest-lead
  name: Biggest Lead
  tracks:
  - track: single-query
    name: Single Query Track
    place: 1
  - track: incremental
    name: Incremental Track
    place: 2
  - track: unsat-core
    name: Unsat Core Track
    place: 1
  - track: model-validation
    name: Model Validation Track
    awards: sequential, parallel, sat
    place: 2
  - track: model-validation
    name: Model Validation Track
    awards: 24s
    place: 3

- award: largest-contribution
  name: Largest Contribution
  tracks:
  - track: single-query
    name: Single Query Track
    awards: sequential, parallel, sat, 24s
    place: 1
  - track: single-query
    name: Single Query Track
    awards: unsat
    place: 2
  - track: incremental
    name: Incremental Track
    awards: parallel
    place: 1
  - track: incremental
    name: Incremental Track
    awards: 24s
    place: 2
  - track: unsat-core
    name: Unsat Core Track
    place: 1
  - track: model-validation
    name: Model Validation Track
    place: 3

---
