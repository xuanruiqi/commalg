From mathcomp Require Import all_ssreflect all_algebra all_fingroup all_field.
Require Import classical basics.

Open Scope ring_scope.
Open Scope classical_set_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Section ideal_lemmas.
  Variables (R : comUnitRingType).

  Notation ideal0 := (pred1 0).

  Lemma ideal0_oppr_closed : @oppr_closed R ideal0.
  Proof.
    move=> x. rewrite /in_mem //= => /eqP ->.
    by rewrite oppr0.
  Qed.

  Lemma ideal0_idealr : GRing.one R != 0 -> @idealr R ideal0.
  Proof.
    move=> non_trivial. 
    apply: MkIdeal; last first.
    rewrite /proper_ideal; split.
    by rewrite /in_mem.
    move=> a x. rewrite /in_mem //=.
    move=> /eqP -> //=. by rewrite mulr0.
  Admitted.
End ideal_lemmas.

Notation ideal0 := (pred1 0).

Section simple.
  Variable (R : ringType).
  Definition simple : Prop :=
     forall (I : {pred R}) (idealrI : idealr I), I =i ideal0.
End simple.
  
Module SimpleRing.
  Import GRing.
  Section axiom.
    Variable R : ringType.
    Definition axiom := simple.
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

    Definition pack b0 (m0 : axiom (@Ring.Pack T b0)) :=
      fun bT b & phant_id (Ring.class bT) b =>
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

    Notation simpleRingType := type.
    Notation SimpleRingType T m:= (@pack T _ m _ _ id _ id).
  End Exports.
End SimpleRing.
