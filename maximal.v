From mathcomp Require Import all_ssreflect all_algebra.
Require Import classical basics.

Open Scope ring_scope.
Open Scope classical_set_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section maximal.
  Definition is_maximal (R : ringType) (S : {pred R}) :=
    forall I, idealr I -> not (S `<=` I).
  
  Structure maximal_idealr (R : ringType) (S : {pred R}) := MkMaximalIdeal  {
    maximal_idealr_zmod :> idealr S ;
    _ : is_maximal S
  }.
End maximal.
