From mathcomp Require Import all_ssreflect all_algebra.
Require Import classical.

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
          (idealrI : idealr I) (idealrJ : idealr J).

Fact is_true_pred_of_set {T} (A : set T) (x : T) : is_true ((pred_of_set A) x) = A x.
Proof. exact: asboolE. Qed.

Fact in_expand {T} (A : {pred T}) (x : T) : x \in A = A x.
Proof. exact. Qed.

Lemma setI_proper_ideal : proper_ideal ((I `&` J) : {pred R}).
Proof.
  have not_1_in : ~ (1 \in I). apply: negP. by case: idealrI => [_ [? _]].
  split.
  apply/negP => //=. rewrite in_setE //= /setI //= => Hc. move: Hc => [not_1_inc _] //=.
  move=> a x. rewrite /in_mem //= /in_set //= !is_true_pred_of_set. 
  move=> []. rewrite -in_expand => xI. rewrite -in_expand => xJ.
  split; rewrite -in_expand.
  by move: idealrI => [_ [_ ->]].
  by move: idealrJ => [_ [_ ->]].
Qed.

Fact setI_key : pred_key (I `&` J). Proof. by []. Qed.
Canonical setI_keyed := KeyedPred setI_key.

Fact setI_addr_closed : addr_closed setI_keyed.
Proof.
  split.
  rewrite in_setE //= /setI //=.
  move: idealrI => [[[_ [zeroI _]] _] _].
  move: idealrJ => [[[_ [zeroJ _]] _] _].
  split; exact.
  move=> x y. rewrite /in_mem //= /in_set //= !is_true_pred_of_set.
  move=> [xI xJ] [yI yJ]. split.
  move: idealrI => [[[_ [_ clI]] _] _]. 
  apply: (clI x y xI yI).
  move: idealrJ => [[[_ [_ clJ]] _] _].
  apply: (clJ x y xJ yJ).
Qed.

Fact setI_oppr_closed : oppr_closed setI_keyed.
Proof.
  move=> x. rewrite in_setE //= /setI //=. move=> [xI xJ].
  rewrite /in_mem //= /in_set //= !is_true_pred_of_set; split.
  move: idealrI => [[[_ [_ _]] clI] _].
  apply: (clI x xI).
  move: idealrJ => [[[_ [_ _]] clJ] _].
  apply: (clJ x xJ).
Qed.

Canonical setI_addrPred := AddrPred setI_addr_closed.
Canonical setI_zmodPred := ZmodPred setI_oppr_closed.

Canonical setI_idealr := MkIdeal setI_zmodPred setI_proper_ideal.
End intersection.

