Require Import Reals.
Require Import Nat.
Require Import Classical_Pred_Type.

(* Both halves of greatestness are stated: 112 is eligible, and every
   eligible positive natural is at most 112. *)
Theorem aime_1987_p8 :
  ((0 < 112)%nat /\
    exists! k : nat,
      (8 / 15 < INR 112 / INR (112 + k))%R /\
      (INR 112 / INR (112 + k) < 7 / 13)%R) /\
  forall n : nat,
    (0 < n)%nat /\
    (exists! k : nat,
      (8 / 15 < INR n / INR (n + k))%R /\
      (INR n / INR (n + k) < 7 / 13)%R) ->
    (n <= 112)%nat.
Proof.
Admitted.
