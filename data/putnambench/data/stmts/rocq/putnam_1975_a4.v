(* Statement-only formalization of PutnamBench artifact putnam_1975_a4:
   an integer-coefficient polynomial expression for the reciprocal of one
   minus a specified complex root of unity. This file contains no proof. *)

From Stdlib Require Import Reals ZArith List Arith.

Import ListNotations.

Definition C := (R * R)%type.

Definition RtoC (x : R) : C := (x, 0%R).
Definition Ci : C := (0%R, 1%R).

Definition Cplus (z w : C) : C :=
  ((fst z + fst w)%R, (snd z + snd w)%R).

Definition Copp (z : C) : C :=
  ((- fst z)%R, (- snd z)%R).

Definition Cminus (z w : C) : C :=
  Cplus z (Copp w).

Definition Cmult (z w : C) : C :=
  ((fst z * fst w - snd z * snd w)%R,
   (fst z * snd w + snd z * fst w)%R).

Definition Cinv (z : C) : C :=
  ((fst z / (fst z ^ 2 + snd z ^ 2))%R,
   (- snd z / (fst z ^ 2 + snd z ^ 2))%R).

Definition Cdiv (z w : C) : C :=
  Cmult z (Cinv w).

Definition Re (z : C) : R := fst z.
Definition Im (z : C) : R := snd z.

Definition complex_exp (z : C) : C :=
  ((exp (Re z) * cos (Im z))%R,
   (exp (Re z) * sin (Im z))%R).

Fixpoint add_integer_polynomials (p q : list Z) : list Z :=
  match p, q with
  | [], _ => q
  | _, [] => p
  | a :: p', b :: q' => (a + b)%Z :: add_integer_polynomials p' q'
  end.

Definition integer_monomial (degree : nat) : list Z :=
  repeat 0%Z degree ++ [1%Z].

Fixpoint sum_odd_monomials (count : nat) : list Z :=
  match count with
  | O => []
  | S k =>
      add_integer_polynomials
        (sum_odd_monomials k)
        (integer_monomial (2 * k + 1))
  end.

Definition putnam_1975_a4_solution (m : nat) : list Z :=
  sum_odd_monomials ((m - 1) / 2).

Fixpoint eval_integer_polynomial (p : list Z) (z : C) : C :=
  match p with
  | [] => RtoC 0
  | a :: p' =>
      Cplus (RtoC (IZR a)) (Cmult z (eval_integer_polynomial p' z))
  end.

Theorem putnam_1975_a4
    (m : nat)
    (hm : (exists k : nat, m = 2 * k + 1) /\ (1 < m)%nat)
    (theta : C)
    (htheta :
      theta =
        complex_exp
          (Cdiv
            (Cmult (RtoC (2 * PI)) Ci)
            (RtoC (INR (2 * m))))) :
  Cdiv (RtoC 1) (Cminus (RtoC 1) theta) =
    eval_integer_polynomial (putnam_1975_a4_solution m) theta.
Admitted.
