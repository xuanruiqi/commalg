From mathcomp Require Import all_ssreflect all_algebra.
Require Import classical basics unit ideal maximal.

Open Scope ring_scope.
Open Scope classical_set_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module LocalRing.
Import GRing.
Section axiom.
Variable (R : ringType).
Definition axiom := forall (I J : {pred R}), @maximal_idealr R I -> maximal_idealr J -> I = J.
End axiom.

Section ClassDef.
Record class_of (R : Type) : Type :=
  Class { base : Ring.class_of R ; mixin : axiom (Ring.Pack base) }.
Local Coercion base : class_of >-> Ring.class_of.

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
End ClassDef.

Module Exports.
Coercion base : class_of >-> Ring.class_of.
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

Notation localRingType := type.
Notation LocalRingType T m:= (@pack T _ m _ _ id _ id).
End Exports.
End LocalRing.
Import LocalRing.Exports.

