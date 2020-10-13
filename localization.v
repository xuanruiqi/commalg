From mathcomp Require Import all_ssreflect all_algebra.
Require Import classical unit ideal maximal local.

Open Scope ring_scope.
Open Scope classical_set_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section multiplicative_set.
Definition mul_closed (R : comRingType) (S : {pred R}) :=
  forall (x y : R), x \in S -> y \in S -> x * y \in S.
End multiplicative_set.

Section localization.
Import GRing.
Open Scope quotient_scope.

Variables (R : comRingType) (S : {pred R}) (closedS : mul_closed S).

Structure tS := MkType { elem : R ; _ : elem \in R }.
Coercion elem : tS >-> GRing.ComRing.sort.

Definition loc_equiv (p p' : R * tS) := 
  match p, p' with
  | (r1, s1), (r2, s2) => `[< exists t, t * (r1 * (s2 : R) - r2 * (s1 : R)) = 0 >]
  end.

Lemma ref_loc_equiv : reflexive loc_equiv.
Proof.
  move=> [r s]. apply/asboolP.
  exists 1. by rewrite subrr mul1r.
Qed.

Lemma sym_loc_equiv : symmetric loc_equiv.
Proof.
  move=> [r1 s1] [r2 s2] => //=. apply: asbool_equiv_eq. split; move=> [t Ht];
  exists t; apply: oppr_inj; rewrite oppr0 -mulNr -mulrN;
  by rewrite opprD addrC mulNr opprK. 
Qed.

Lemma trans_loc_equiv : transitive loc_equiv.
Proof.
  move=> [r1 s1] [r2 s2] [r3 s3] /asboolP [t1 H1] /asboolP [t2 H2].
  apply/asboolP.
Admitted.

Definition eqrel_loc_equiv := EquivRel loc_equiv ref_loc_equiv sym_loc_equiv trans_loc_equiv.
Canonical eqrel_loc_equiv.
End localization.
