(* Statement-only formalization of PutnamBench artifact putnam_1986_b3:
   lifting a factorization of an integer polynomial modulo a prime to a
   factorization modulo an arbitrary positive power. This file contains no
   proof. *)

From Stdlib Require Import ZArith Znumtheory Lists.List Arith.

Import ListNotations.

Definition putnam_1986_b3_polynomial : Type := list Z.

Definition putnam_1986_b3_coefficient
    (f : putnam_1986_b3_polynomial) (i : nat) : Z :=
  nth i f 0%Z.

Fixpoint putnam_1986_b3_add
    (f g : putnam_1986_b3_polynomial) :
    putnam_1986_b3_polynomial :=
  match f, g with
  | [], _ => g
  | _, [] => f
  | a :: f', b :: g' =>
      (a + b)%Z :: putnam_1986_b3_add f' g'
  end.

Fixpoint putnam_1986_b3_scale
    (a : Z) (f : putnam_1986_b3_polynomial) :
    putnam_1986_b3_polynomial :=
  match f with
  | [] => []
  | b :: f' => (a * b)%Z :: putnam_1986_b3_scale a f'
  end.

Fixpoint putnam_1986_b3_mul
    (f g : putnam_1986_b3_polynomial) :
    putnam_1986_b3_polynomial :=
  match f with
  | [] => []
  | a :: f' =>
      putnam_1986_b3_add
        (putnam_1986_b3_scale a g)
        (0%Z :: putnam_1986_b3_mul f' g)
  end.

Definition putnam_1986_b3_congruent
    (f g : putnam_1986_b3_polynomial) (m : Z) : Prop :=
  forall i : nat,
    exists k : Z,
      (putnam_1986_b3_coefficient f i -
       putnam_1986_b3_coefficient g i = m * k)%Z.

Theorem putnam_1986_b3
    (n p : nat)
    (nppos : (0 < n)%nat /\ (0 < p)%nat)
    (pprime : prime (Z.of_nat p))
    (f g h r s : putnam_1986_b3_polynomial)
    (hcoprime :
      putnam_1986_b3_congruent
        (putnam_1986_b3_add
          (putnam_1986_b3_mul r f)
          (putnam_1986_b3_mul s g))
        [1%Z]
        (Z.of_nat p))
    (hprod :
      putnam_1986_b3_congruent
        (putnam_1986_b3_mul f g) h (Z.of_nat p)) :
  exists F G : putnam_1986_b3_polynomial,
    putnam_1986_b3_congruent F f (Z.of_nat p) /\
    putnam_1986_b3_congruent G g (Z.of_nat p) /\
    putnam_1986_b3_congruent
      (putnam_1986_b3_mul F G) h (Z.of_nat (Nat.pow p n)).
Admitted.
