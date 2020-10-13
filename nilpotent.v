From mathcomp Require Import all_ssreflect all_algebra.
Require Import classical unit ideal.

Open Scope ring_scope.
Open Scope classical_set_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section nilpotent.
Import GRing.

Variable (R : comUnitRingType).

Definition nilpotentP (x : R) := exists n, x ^+ n == 0.
Definition nilpotent (x : R) := `[< nilpotentP x >].

(* Next: the set of nilpotents (i.e., nilradical) of R forms an ideal *)
Lemma nilpotent_proper_ideal : proper_ideal nilpotent.
Proof.
  split => //=. rewrite /in_mem //=. apply/asboolPn.
  rewrite -forallNE => n. apply/negP. by rewrite expr1n oner_neq0.
  move=> x y. rewrite /in_mem //= => /asboolPn /contrapT [n Hn]. 
  apply/asboolPn. rewrite eqNN. exists n.
  rewrite exprMn_comm.
  move: Hn => /eqP ->. by rewrite mulr0.
  by rewrite /comm mulrC.
Qed.

Fact nilpotent_key : pred_key nilpotent. Proof. by []. Qed.
Canonical nilpotent_keyed := KeyedPred nilpotent_key.

Fact index_size (i m n : nat) : (i < (m + n).+1)%N -> ((m + n - i) >= n)%N || (i >= m)%N.
Proof.
  rewrite ltnS. move=> ib.
  case_eq (m <= i)%N => m_sz. by rewrite orbT.
  rewrite orbF.
  move/negbT: m_sz. rewrite -ltnNge => i_lt_m.
  rewrite addnC -addnBA; last first.
  by rewrite leq_eqVlt i_lt_m orbT.
  by rewrite -[X in (X <= _)%N]addn0 leq_add2l.
Qed.

Fact sumr_zero_guard m (F : nat -> R) :
  (forall i, (i < m)%N -> F i = 0) -> \sum_(i < m) F i = 0.
Proof.
  move=> guard.
  rewrite (eq_bigr (fun _ => 0)) //=.
  by rewrite sumr_const //= mul0rn.
  move=> i _. by rewrite guard.
Qed.

Fact largepow_0 (x : R) (n m : nat) : x ^+ n = 0 -> (n <= m)%N -> x ^+ m = 0.
Proof.
  move=> nilp n_le_m.
  by rewrite -(subnKC n_le_m) exprD nilp mul0r.
Qed.

Lemma nilpotent_addr_closed : addr_closed nilpotent_keyed.
Proof.
  split.
  rewrite /in_mem //=. apply/asboolPn. rewrite eqNN.
  exists 1%N. by rewrite expr0n.
  move=> x y. 
  rewrite /in_mem //= => /asboolPn /contrapT [n /eqP nilp_n] /asboolPn /contrapT [m /eqP nilp_m].
  apply/asboolPn. rewrite eqNN.
  (* Proof by binomial theorem: at least one binomial exponent is large enough *)
  (* We take the exponent to be m + n but this is certainly not minimal *)
  exists (m + n)%N.
  rewrite exprDn.
  have tm_zero i : (i < (m + n).+1)%N -> x ^+ (m + n - i) * y ^+ i *+ 'C(m + n, i) = 0.
  move=> ib. have := (index_size ib) => /orP H. case: H => [Hm | Hn].
  by rewrite (largepow_0 nilp_n Hm) mul0r mul0rn.
  by rewrite (largepow_0 nilp_m Hn) mulr0 mul0rn.
  by rewrite (sumr_zero_guard tm_zero).
Qed.

Fact nilpotent_oppr_closed : oppr_closed nilpotent_keyed.
Proof.
  move=> x. rewrite /in_mem //= => /asboolPn /contrapT [n /eqP Hn].
  apply/asboolPn. rewrite eqNN. exists n.
  by rewrite exprNn Hn mulr0.
Qed.

Canonical nilpotent_addrPred := AddrPred nilpotent_addr_closed.
Canonical nilpotent_zmodPred := ZmodPred nilpotent_oppr_closed.

Canonical nilpotent_idealr := MkIdeal nilpotent_zmodPred nilpotent_proper_ideal.
End nilpotent.

(* The nilradical of a commutative ring *)
Notation Nil R := (nilpotent_idealr R).
