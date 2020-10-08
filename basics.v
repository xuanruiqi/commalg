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

