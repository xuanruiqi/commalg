From mathcomp Require Import all_ssreflect all_algebra.
Require Import classical basics.

Open Scope ring_scope.
Open Scope classical_set_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Some basic facts about ideas, not contained within ring_quotient.v *)

Import GRing.Theory.
Section trivial_ideal.
  Variables (R : comUnitRingType).
  Local Notation ideal0 := (@pred1 R 0).

  Fact ideal0_key : pred_key ideal0. Proof. by []. Qed.
  Canonical ideal0_keyed := KeyedPred ideal0_key.
  
  Fact ideal0_addr_closed : addr_closed ideal0_keyed.
  Proof.
    split.
    rewrite /in_mem //=.
    move=> x y. rewrite /in_mem //= => /eqP -> /eqP ->.
    by rewrite add0r.
  Qed.

  Fact ideal0_oppr_closed : oppr_closed ideal0_keyed.
  Proof.
    move=> x. rewrite /in_mem //= => /eqP ->.
    by rewrite oppr0.
  Qed.
  
  Canonical ideal0_addrPred := AddrPred ideal0_addr_closed.
  Canonical ideal0_zmodPred := ZmodPred ideal0_oppr_closed.

  Lemma ideal0_proper_ideal : proper_ideal ideal0.
  Proof.
    split. rewrite /in_mem //=. apply: oner_neq0.
    move=> a x. rewrite /in_mem //= => /eqP ->. by rewrite mulr0.
  Qed.
    
  Canonical ideal0_idealr := MkIdeal ideal0_zmodPred ideal0_proper_ideal.
End trivial_ideal.
Notation ideal0 := (pred1 0).

Section intersection.
Local Definition pred_of_set {T} (p : set T) : {pred T} := asbool \o p.
Local Coercion pred_of_set : set >-> pred_sort.

Variables (R : ringType) (I J : {pred R}) 
          (idealrI : idealr I) (idealrJ : idealr J)
          (kI : keyed_pred idealrI) (kJ : keyed_pred idealrJ).

Lemma idealr1' : 1 \in kI = false.
Proof. by apply: negPf; case: idealrI kI => ? /= [? _] [] /= _ ->. Qed.

Lemma proper_idealI : proper_ideal (I `&` J).
Proof.
  have not_1_in : ~ (1 \in I). apply: negP. by case: idealrI kI => ? //= [? _] [] //= _.
  split.
  apply/negP => //=. rewrite in_setE //= /setI //= => Hc. move: Hc => [not_1_inc _] //=.
  move=> a x.
Admitted.
End intersection.
