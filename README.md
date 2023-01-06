# Commutative algebra in Coq/SSReflect

Commutative algebra formalized in Coq using SSReflect/MathComp & packed classes. This repository is
part of the [Coq/SSReflect algebraic geometry project](https://www.xuanruiqi.com/algebraic-geometry/).

The development currently consists of the following files:

* [classical.v](classical.v): exports libraries required for classical reasoning, and some additional lemmas. Currently,
  we assume functional extensionality, `Prop` extensionality, decidable equality for every type, and the (type-theoretic)
  Axiom of Choice. The Axiom of Choice, in particular, is required to prove statements such as Krull's theorem;
* [unit.v](unit.v): unitRing structure for every ring (from classical reasoning);
* [ideal.v](ideal.v): some facts about ideals (e.g., intersection of ideals is an ideal);
* [maximal.v](maximal.v): defines maximal ideals and lemmas about them. Currently, we are working on proving Krull's
  theorem (every nonzero ring has a maximal ideal);
* [noetherian.v](noetherian.v): defines Noetherian rings. Two goal theorems are: (1) a ring is Noetherian iff every ideal is
  finitely generated, and (2) Hilbert's basis theorem (R[x] is Noetherian if R is Noetherian);
* [local.v](local.v): basic facts about local rings;
* [localization.v](localization.v): the localization of a ring, one of the most important constructions in algebraic geometry;
* [nilpotent.v](nilpotent.v): facts about nilpotents and the nilradical of a ring.

All rings here are commutative and have 1, as is conventional in commutative algebra. We don't really have a canonical
reference here, but we often refer to:

* David Eisenbud, _Commutative Algebra with a View Toward Algebraic Geometry_ (i.e., GTM 150);
* M. F. Atiyah & I. G. MacDonald, _Introduction to Commutative Algebra_;
* and the [Stacks Project](https://stacks.math.columbia.edu/).

## Usage
Install necessary dependencies:

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-mathcomp-ssreflect coq-mathcomp-algebra coq-mathcomp-classical
```

and then run `make`.

Alternatively, use opam: `opam pin .` then `opam install`.

## Author
Xuanrui Qi ([xuanrui@nagoya-u.jp](mailto:xuanrui@nagoya-u.jp), [me@xuanruiqi.com](mailto:me@xuanruiqi.com)),
with the assistance of:

* [Reynald Affeldt](https://staff.aist.go.jp/reynald.affeldt/) (affeldt-aist)
* [Takafumi Saikawa](https://github.com/t6s)

## License
MIT License
