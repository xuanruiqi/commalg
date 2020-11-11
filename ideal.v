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

(* The radical of an ideal is an ideal *)
Section radical.
Variables (R : comRingType) (I : {pred R}) (idealI : idealr I).

Definition radical x := `[< exists n : nat, x ^+ n \in I >].

Lemma radical_proper_ideal : proper_ideal radical.
Proof.
  split.
  move: idealI => [_ [one_notinI _]].
  rewrite /in_mem //=. apply/negP => //=.
  rewrite in_setE -forallNE => n.
  rewrite expr1n /in_mem //=. 
  move: one_notinI. by rewrite /in_mem //= => /negP.
  move=> a x. rewrite /in_mem //= => /asboolP [n x_pow_n].
  apply/asboolP. exists n. rewrite exprMn_comm. 
  move: idealI => [_ [_ closedI]].
  apply: (closedI (a ^+ n) (x ^+ n) x_pow_n).
  apply: mulrC.
Qed.

Fact radical_key : pred_key radical. Proof. by []. Qed.
Canonical radical_keyed := KeyedPred radical_key.

Lemma mulrn_closed x n : x \in I -> x *+ n \in I.
Proof.
  move=> xI. elim: n => [| n IH] //=.
  rewrite mulr0n. by move: idealI => [[[_ [-> _]] _] _].
  rewrite mulrSr.
  move: idealI => [[[_ [_ Hin]] _] _].
  by apply: Hin.
Qed.

Lemma radical_addr_closed : addr_closed radical.
Proof.
  have mul_closed: forall a x, x \in I -> a * x \in I.
  move: idealI => [_ [_ H]]. apply: H.
  split.
  apply/asboolP. exists 1%N. rewrite expr0n //=.
  by move: idealI => [[[_ [-> _]] _] _].
  move=> x y. rewrite /in_mem //= => /asboolP [n x_pow_n].
  move=> /asboolP [m y_pow_m]. apply/asboolP.
  exists (m + n)%N. rewrite exprDn.
  have tm_in_I: forall i, (i < (m + n).+1)%N -> x ^+ (m + n - i)%N * y ^+ i *+ 'C(m + n, i) \in I.
  move=> i i_bound.
  case_eq (i < m)%N => //= i_cond.
  have x_pow_in_I: x ^+ (m + n - i) \in I.
  rewrite addnC -addnBA. rewrite exprD mulrC.
  by apply: mul_closed. by rewrite leq_eqVlt i_cond orbT.
  rewrite mulrC. apply: mulrn_closed. by apply: mul_closed.
  have y_pow_in_I : y ^+ i \in I.
  rewrite -(@subnKC m i). rewrite exprD mulrC. by apply: mul_closed.
  by rewrite leqNgt i_cond. apply: mulrn_closed. by apply: mul_closed.
Admitted.

Lemma radical_oppr_closed : oppr_closed radical.
Proof.
  move=> x. rewrite /in_mem //= => /asboolP [n xpow_I].
  apply/asboolP. exists n. rewrite exprNn.
  by move: idealI => [_ [_ ->]].
Qed.

End radical.
