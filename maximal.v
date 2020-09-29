From mathcomp Require Import all_ssreflect all_algebra.
Require Import classical basics ideal.

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

Section maximal_equiv.
  Import Quotient.
  Import GRing.
  
  Variables (R : comUnitRingType) (I : {pred R}) (idealI : idealr I).
  Variable (kI : keyed_pred idealI).
  
  Notation quotRI := (@rquot_ringQuotType R I idealI kI).

  (* Need to first prove that the quotient of a ring with 1 has 1 *)
  (* Lemma maximal_quot_simple : maximal_idealr I -> Field.mixin_of quotRI. *)
End maximal_equiv.

Section krull.
  Variables (R : unitRingType).

  (* Krull's theorem: every non-trivial ring has a maximal ideal *)
  Theorem has_maximal_ideal : GRing.one R != 0 -> exists I : {pred R}, maximal_idealr I.
  Admitted.
End krull.
