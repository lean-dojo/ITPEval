(*
  Statement-only formalization of Thousand Theorems corpus artifact Q791663
  (thousand-theorems__rocq__Q791663), "Beatty's theorem": conjugate real
  parameters give complementary two-sided Beatty sequences, and when the
  first parameter is irrational their positive Beatty sequences partition
  the positive integers. This file contains no proof.
*)

From Stdlib Require Import Reals QArith ZArith.ZArith.

Local Open Scope R_scope.

Definition q791663_holder_conjugate (r s : R) : Prop :=
  0 < r /\ 0 < s /\ / r + / s = 1.

Definition q791663_irrational (r : R) : Prop :=
  ~ exists q : Q, r = Q2R q.

Definition q791663_is_floor (x : R) (n : Z) : Prop :=
  IZR n <= x < IZR (n + 1)%Z.

Definition q791663_is_ceil_minus_one (x : R) (n : Z) : Prop :=
  IZR n < x <= IZR (n + 1)%Z.

Definition q791663_beatty (r : R) (n : Z) : Prop :=
  exists k : Z,
    q791663_is_floor (IZR k * r) n.

Definition q791663_beatty_prime (r : R) (n : Z) : Prop :=
  exists k : Z,
    q791663_is_ceil_minus_one (IZR k * r) n.

Definition q791663_beatty_pos (r : R) (n : Z) : Prop :=
  exists k : Z,
    (0 < k)%Z /\
    q791663_is_floor (IZR k * r) n.

Theorem compl_beattySeq :
  forall r s : R,
    q791663_holder_conjugate r s ->
    forall n : Z,
      ~ q791663_beatty r n <-> q791663_beatty_prime s n.
Proof.
Admitted.

Module Irrational.

Theorem beattySeq_symmDiff_beattySeq_pos :
  forall r s : R,
    q791663_holder_conjugate r s ->
    q791663_irrational r ->
    forall n : Z,
      ((q791663_beatty_pos r n /\ ~ q791663_beatty_pos s n) \/
       (q791663_beatty_pos s n /\ ~ q791663_beatty_pos r n)) <->
      (0 < n)%Z.
Proof.
Admitted.

End Irrational.
