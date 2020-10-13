From mathcomp Require Import all_ssreflect all_algebra.
Require Import classical unit ideal.

Open Scope ring_scope.
Open Scope classical_set_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section ascending_chain.
Variable (R : comRingType).

(* A chain of ideals I_1, I_2, ..., I_n, ... *)
Variable (chain : nat -> {pred R}).

(* The ascending chain condition *)
Definition asc_chain :=
  (* the chain is actually a chain of ideals *)
  (forall n, idealr (chain n)) ->
  (* the chain is well-formed *)
  (forall m n, (m <= n)%nat -> chain m `<=` chain n)
  -> exists m, forall n, (n >= m)%nat -> chain m =i \bigcup_(i : nat) (chain i).
End ascending_chain.

Module NoetherianRing.
Import GRing.
Section axiom.
Variable (R : comRingType).
Definition axiom := forall (chain : nat -> {pred R}), asc_chain chain.
End axiom.

Section ClassDef.
Record class_of (R : Type) : Type :=
  Class { base : ComRing.class_of R ; mixin : axiom (ComRing.Pack base) }.
Local Coercion base : class_of >-> ComRing.class_of.
  
Structure type := Pack { sort ; _ : class_of sort }.
Local Coercion sort : type >-> Sortclass.
Variable (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).
  
Definition pack b0 (m0 : axiom (@ComUnitRing.Pack T b0)) :=
  fun bT b & phant_id (ComUnitRing.class bT) b =>
    fun    m & phant_id m0 m => Pack (@Class T b m).
  
Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition zmodType := @Zmodule.Pack cT xclass.
Definition ringType := @Ring.Pack cT xclass.
Definition comRingType := @ComRing.Pack cT xclass.
End ClassDef.

Module Exports.
Coercion base : class_of >-> ComRing.class_of.
Arguments mixin [R] c.
Coercion mixin : class_of >-> axiom.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.

Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> Ring.type.
Canonical ringType.
Coercion comRingType : type >-> ComRing.type.
Canonical comRingType.

Notation noetherianRingType := type.
Notation NoetherianRingType T m:= (@pack T _ m _ _ id _ id).
End Exports.
End NoetherianRing.
Import NoetherianRing.Exports.

Section noetherian_asc_chain.
Lemma noetherian_asc_chain (R : noetherianRingType) (chain : nat -> {pred R}) : asc_chain chain.
Proof.
  move: R chain => [R [? //=]].
Qed.
End noetherian_asc_chain.

Export NoetherianRing.Exports.
