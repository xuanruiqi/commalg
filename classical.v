From mathcomp Require Import all_ssreflect.
From mathcomp.analysis Require Export classical_sets boolp.
Require Export FunctionalExtensionality ProofIrrelevanceFacts ProofIrrelevance.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma asboolbK (b : bool) : `[< b >] = b.
Proof.
  case: b => //=.
  by apply/asboolP.
  by apply: asboolF.
Qed.
