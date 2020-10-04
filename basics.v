From mathcomp Require Import all_ssreflect all_algebra.
Require Import classical.

Open Scope ring_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* basics.v : preliminary definitions given as granted in the Stacks Project *)

Section elem.
  (* All base rings are commutative with unit *)
  Variable (R : comUnitRingType).

  Definition nilpotent (x : R) := exists n, x ^ n = 0.
  Definition zero_divisor (x : R) := exists y, x * y = 0.
  Definition idempotent (e : R) := e * e = e.
End elem.

(* Since we are classical, every ringType is a unitRingType *)
Section unit_ring.
  Variable (R : ringType).

  Definition is_inv (x y : R) := (x * y == 1) && (y * x == 1).
  Definition unitP (x : R) := exists y : R, is_inv x y.
  Definition unitB x : bool := `[< unitP x >].

  Fact unitP_inv_right (x : R) : unitP x -> exists y, x * y == 1.
  Proof. move=> [y /andP [invr _]]. by exists y. Qed.

  Fact unitP_inv_left (x : R) : unitP x -> exists y, y * x == 1.
  Proof. move=> [y /andP [_ invl]]. by exists y. Qed.
  
  Definition invS x :=
    match pselect (unitP x) with
    | left ex_inv => xchoose ex_inv
    | right _ => x
    end.

  Fact invE x : unitP x -> (x * invS x == 1) && (invS x * x == 1).
  Proof.
    move=> is_unit. rewrite /invS.
    case: (pselect (unitP x)) => H; last first. exact.
    apply: (xchooseP H).
  Qed.
  
  Fact R_mulVr : {in unitB, left_inverse 1 invS *%R}.
  Proof.
    move=> x. rewrite /in_mem //= => /asboolP is_unit.
    set H' := (invE is_unit). by move/andP: H' => [_ /eqP ->]. 
  Qed.

  Fact R_divrr : {in unitB, right_inverse 1 invS *%R}.
  Proof.
    move=> x. rewrite /in_mem //= => /asboolP is_unit.
    set H' := (invE is_unit). by move/andP: H' => [/eqP -> _]. 
  Qed.

  Fact R_mulVrr_unit (x y : R) : y * x = 1 /\ x * y = 1 -> unitB x.
  Proof.
    move=> [invl invr].
    apply/asboolP. exists y. apply/andP.
    split; by apply/eqP.
  Qed.

  Fact R_inv_out : {in [predC unitB], invS =1 id}.
  Proof.
    move=> x. Locate "[ predC _ ]".
    rewrite /predC //= /in_mem //=. move/asboolPn => not_unit.
    rewrite /invS. by case: (pselect (unitP x)).
  Qed.

  Definition ring_unitRingMixin := UnitRingMixin R_mulVr R_divrr R_mulVrr_unit R_inv_out.
  Canonical ring_unitRingType := Eval hnf in UnitRingType R ring_unitRingMixin.
End unit_ring.

