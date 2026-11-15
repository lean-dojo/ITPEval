From mathcomp Require Import all_boot all_algebra all_field archimedean.
Require Import gauss_int.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory UnityRootTheory.

Open Scope nat_scope.

Definition sum_of_two_square := 
  [qualify a x |
       [exists a : 'I_x.+1, exists b : 'I_x.+1, x == a ^ 2 + b ^ 2]].

Lemma sum2sP x :
  reflect (exists m, exists n, x = m ^ 2 + n ^ 2) 
          (x \is a sum_of_two_square).
Proof.
Admitted.

Fact sum2s0 : 0 \is a sum_of_two_square.
Proof.
Admitted.

Fact sum2s1 : 1 \is a sum_of_two_square.
Proof.
Admitted.

Fact sum2s2 : 2 \is a sum_of_two_square.
Proof.
Admitted.

Fact sum2sX_even x n :
 ~~ odd n  -> x ^ n \is  a sum_of_two_square.
Proof.
Admitted.

Lemma sum2sGP x :
  reflect (exists m : GI, x = normGI m)
          (x \is a sum_of_two_square).
Proof.
Admitted.

Lemma sum2sM x y :
  x \is  a sum_of_two_square ->
  y \is  a sum_of_two_square ->
  x * y \is  a sum_of_two_square.
Proof.
Admitted.

Lemma sum2s_dvd_prime p a b :
  prime p -> coprime a b -> 
  p %| a ^ 2 + b ^ 2 -> p \is  a sum_of_two_square.
Proof.
Admitted.

Lemma sum2sX x n :
  x \is  a sum_of_two_square  -> x ^ n \is  a sum_of_two_square.
Proof.
Admitted.

Lemma sum2sX_prime x n :
  prime x -> odd n ->
  x ^ n \is  a sum_of_two_square -> x  \is  a sum_of_two_square.
Proof.
Admitted.

Lemma sum2sM_coprime x y :
  coprime x y ->
  x * y \is  a sum_of_two_square ->  x \is  a sum_of_two_square.
Proof.
Admitted.

Lemma modn_prod I r (P : pred I) F d :
  \prod_(i <- r | P i) (F i %% d) = \prod_(i <- r | P i) F i %[mod d].
Proof.
Admitted.

Lemma sum2sprime p : 
  odd p -> prime p -> p \is a sum_of_two_square = (p %% 4 == 1).
Proof.
Admitted.

(** Main theorem **)
Lemma sum2stest n :
  reflect
  (forall p,  prime p -> odd p -> p %| n -> odd (logn p n) -> p %% 4 = 1)
  (n \is a sum_of_two_square).
Proof.
Admitted.
