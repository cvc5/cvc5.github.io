---
layout: artifact

title: Bit-Precise Reasoning via Int-Blasting
conference: FMCAD 2021
submission: yes

pdf:

authors:
- name: Yoni Zohar
  url: https://cs.stanford.edu/~yoniz
- name: Ahmed Irfan
  url: https://ahmed-irfan.github.io/
- name: Makai Mann
  url: https://makaimann.github.io/
- name: Aina Niemetz
  url: https://cs.stanford.edu/~niemetz/
- name: Andres Noetzli
  url: https://cs.stanford.edu/people/noetzli/
- name: Mathias Preiner
  url: https://cs.stanford.edu/~preiner/
- name: Andrew Reynolds
  url: http://cs.uiowa.edu/~ajreynol/
- name: Clark Barrett
  url: http://theory.stanford.edu/~barrett/
- name: Cesare Tinelli
  url: http://homepage.cs.uiowa.edu/~tinelli/

artifact:
  readme: https://cvc4.cs.stanford.edu/papers/FMCAD2021-intblast/README
  archive: https://cvc4.cs.stanford.edu/papers/FMCAD2021-intblast/artifact.tar.gz
  ext: tar.gz
  text: all materials
---
A branch of cvc5 that contains the source code for the implementation is
available [here](https://github.com/yoni206/CVC5/tree/bv_to_int_module).
The most relevant source files are:
[int_blaster.cpp](https://github.com/yoni206/CVC5/blob/bv_to_int_module/src/theory/bv/int_blaster.cpp) and
[iand_solver.cpp](https://github.com/yoni206/CVC5/blob/bv_to_int_module/src/theory/arith/nl/iand_solver.cpp).
