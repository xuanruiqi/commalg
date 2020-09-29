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
  Import GRing. Search eqType.
  About gen_eqMixin.
  
  Variables (R : comRingType) (I : {pred R}) (idealI : idealr I).
  Variable (kI : keyed_pred idealI).
  
  Notation quotRI := (ring_unitRingType (rquot_ringQuotType kI)).

  Lemma maximal_quot_simple : maximal_idealr I -> Field.mixin_of quotRI.
  Proof.
    move=> maximalI x x_neq_0. rewrite /in_mem //=.
  Admitted.
End maximal_equiv.

Section krull.
  Variables (R : unitRingType).

  (* Krull's theorem: every non-trivial ring has a maximal ideal *)
  Theorem has_maximal_ideal : GRing.one R != 0 -> exists I : {pred R}, maximal_idealr I.
  Admitted.
End krull.
