# Commutative algebra in Coq/SSReflect

Commutative algebra formalized in Coq using SSReflect/MathComp & packed classes. This repository is 
part of the [Coq/SSReflect algebraic geometry project](https://www.xuanruiqi.com/algebraic-geometry/). 

The development currently consists of the following files:

* [classical.v](classical.v): exports libraries required for classical reasoning, and some additional lemmas. Currently, 
  we assume functional extensionality, `Prop` extensionality, decidable equality for every type, and the (type-theoretic) 
  Axiom of Choice. The Axiom of Choice, in particular, is required to prove statements such as Krull's theorem;
* [basics.v](basics.v): defines some helpful notions (e.g., zero divisors);
* [maximal.v](maximal.v): defines maximal ideals and lemmas about them. Currently, we are working on proving Krull's 
  theorem (every nonzero ring has a maximal ideal);
* [noetherian.v](noetherian.v): defines Noetherian rings. Two goal theorems are: (1) a ring is Noetherian iff every ideal is
  finitely generated, and (2) Hilbert's basis theorem (R[x] is Noetherian if R is Noetherian).

All rings here are commutative and has 1, as is conventional in commutative algebra.

## Usage
Generate the Makefile:

    coq_makefile -f _CoqProject -o Makefile

and then run `make`.

## Author
Xuanrui Qi ([xuanrui@nagoya-u.jp](mailto:xuanrui@nagoya-u.jp), [me@xuanruiqi.com](mailto:me@xuanruiqi.com)),
with the assistance of:

* [Reynald Affeldt](https://staff.aist.go.jp/reynald.affeldt/) (affeldt-aist)
* [Takafumi Saikawa](https://github.com/t6s)

## License
MIT License
