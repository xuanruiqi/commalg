From mathcomp Require Import all_ssreflect all_algebra.
Require Import classical basics unit ideal.

Open Scope ring_scope.
Open Scope classical_set_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* This is a temporary fix; we probably need more infrastructure to work with this. *)
Definition pred_of_set {T} (p : set T) := asbool \o p.

Fact set_display : unit. Proof. by []. Qed.

Section maximal.
Definition is_maximal (R : ringType) (S : {pred R}) :=
  forall I, idealr I -> S <> I -> not (S `<=` I).

Structure maximal_idealr (R : ringType) (S : {pred R}) := MkMaximalIdeal
{
  maximal_idealr_ideal :> idealr S ;
  _ : is_maximal S ;
}.
End maximal.

Section maximal_equiv.
Import Quotient GRing.

Variables (R : comRingType) (I : {pred R})
          (idealI : idealr I) (kI : keyed_pred idealI).

Notation quotRI := (rquot_ringQuotType kI).

Lemma maximal_quot_field : maximal_idealr I -> Field.mixin_of quotRI.
Proof.
  move=> maximalI x x_neq_0. rewrite /in_mem //=.
Admitted.

Lemma quot_field_maximal : Field.mixin_of quotRI -> maximal_idealr I.
Proof.
  rewrite /Field.mixin_of /in_mem //= => quot_fieldAx.
Admitted.
End maximal_equiv.

Section krull.
Variables (R : unitRingType).

Structure ideal := MkIdeal { idealS : set R; _ : idealr (pred_of_set idealS) }.
Coercion idealS : ideal >-> set.

(* Section IdealOrder.
   Implicit Types (X Y : set ideal).
   
   Lemma setI_meet X Y : `[< X `<=` Y >] = (X `&` Y == X).
   Proof. by apply/asboolP/eqP; rewrite setIidPl. Qed.
   
   Fact SetOrder_joinKI (Y X : set ideal) : X `&` (X `|` Y) = X.
   Proof. Admitted.
   
   Fact SetOrder_meetKU (Y X : set ideal) : X `|` (X `&` Y) = X.
   Proof. Admitted.
   
   Fact SetOrder_ldist : left_distributive (@setI ideal) setU.
   Admitted.
   
   Definition orderMixin := @MeetJoinMixin _ _ _ setI setU setI_meet
   (fun _ _ => erefl) (@setIC _) (@setUC _) (@setIA _) (@setUA _)
   SetOrder_joinKI SetOrder_meetKU SetOrder_ldist setIid.
   
   Canonical idealSet_porderType := POrderType set_display _ orderMixin.
   End IdealOrder. 
 *)

(* R := subset *)
Lemma ideal_incl_trans (I J S : ideal) : I `<=` J -> J `<=` S -> I `<=` S.
Proof. exact: subset_trans. Qed.

Lemma ideal_incl_antisym (I J : ideal) : I `<=` J -> J `<=` I -> I = J.
Proof.
  move: I J => [setI idI] [setJ idJ] //= setIJ setJI.
  have setEq := eqEsubset setIJ setJI.
  subst; congr MkIdeal. apply: Prop_irrelevance.
Qed.

Lemma has_upper_bound (P : set ideal) : 
  total_on P subset -> exists (S : ideal), forall (I : ideal), P I -> I `<=` S.
Proof. 
  rewrite /total_on.
  move=> is_total. 
Admitted.

Lemma pred_of_setE {T} (S : {pred T}) : pred_of_set S = S.
Proof. rewrite /pred_of_set funeqE => x //=. exact: asboolbK. Qed.

(* Krull's theorem: every non-trivial ring has a maximal ideal *)
Theorem has_maximal_ideal : exists I : {pred R}, maximal_idealr I.
Proof.
  have [M maximal_M] := (Zorn (fun _ _ => ssrfun.id) ideal_incl_trans ideal_incl_antisym has_upper_bound).
  exists (pred_of_set M). split => //. by move: M maximal_M => [setM ideal_M] _.
  rewrite /is_maximal.
  move => setI ideal_I.
  have ideal_sI : idealr (pred_of_set setI) by rewrite pred_of_setE.
  have := (maximal_M (MkIdeal ideal_sI)).
  move/contrap.
  (* forall I, idealr I -> not (S `<=` I). <-> forall I, I `<=` S -> I = S *)
Admitted.
End krull.
