From mathcomp Require Import all_ssreflect.
From mathcomp.analysis Require Export classical_sets boolp.
Require Export FunctionalExtensionality ProofIrrelevanceFacts ProofIrrelevance.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma funext (A B : Type) (f g : A -> B) : f =1 g -> f = g.
Proof.
  move=> H. extensionality x. apply: H.
Qed.


