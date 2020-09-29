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

  Search keyed_pred.
  About KeyedPred.

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

