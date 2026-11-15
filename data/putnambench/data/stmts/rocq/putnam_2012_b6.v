(* Statement-only formalization of PutnamBench corpus artifact putnam_2012_b6:
   the parity of the cubing permutation on residue classes modulo an odd prime
   p congruent to 2 modulo 3. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Vectors.Fin.

Import ListNotations.

Definition putnam_2012_b6_prime (p : nat) : Prop :=
  2 <= p /\
  forall d : nat, Nat.divide d p -> d = 1 \/ d = p.

Record putnam_2012_b6_permutation (p : nat) : Type := {
  putnam_2012_b6_perm_fun : Fin.t p -> Fin.t p;
  putnam_2012_b6_perm_inv : Fin.t p -> Fin.t p;
  putnam_2012_b6_perm_inv_l :
    forall x : Fin.t p,
      putnam_2012_b6_perm_inv (putnam_2012_b6_perm_fun x) = x;
  putnam_2012_b6_perm_inv_r :
    forall x : Fin.t p,
      putnam_2012_b6_perm_fun (putnam_2012_b6_perm_inv x) = x
}.

Definition putnam_2012_b6_swap {p : nat}
    (a b x : Fin.t p) : Fin.t p :=
  if Fin.eq_dec x a then b
  else if Fin.eq_dec x b then a
  else x.

Fixpoint putnam_2012_b6_apply_transpositions {p : nat}
    (swaps : list (Fin.t p * Fin.t p)) (x : Fin.t p) : Fin.t p :=
  match swaps with
  | [] => x
  | (a, b) :: rest =>
      putnam_2012_b6_swap a b
        (putnam_2012_b6_apply_transpositions rest x)
  end.

Definition putnam_2012_b6_even {p : nat}
    (P : putnam_2012_b6_permutation p) : Prop :=
  exists (swaps : list (Fin.t p * Fin.t p)) (k : nat),
    Forall (fun swap => fst swap <> snd swap) swaps /\
    length swaps = 2 * k /\
    forall x : Fin.t p,
      putnam_2012_b6_apply_transpositions swaps x =
      putnam_2012_b6_perm_fun p P x.

Definition putnam_2012_b6_residue {p : nat} (x : Fin.t p) : nat :=
  proj1_sig (Fin.to_nat x).

Theorem putnam_2012_b6
    (p : nat)
    (hpodd : Nat.Odd p)
    (hpprime : putnam_2012_b6_prime p)
    (hpmod3 : Nat.modulo p 3 = 2)
    (P : putnam_2012_b6_permutation p)
    (hP : forall x : Fin.t p,
      putnam_2012_b6_residue (putnam_2012_b6_perm_fun p P x) =
      Nat.modulo
        (putnam_2012_b6_residue x *
         putnam_2012_b6_residue x *
         putnam_2012_b6_residue x) p) :
  putnam_2012_b6_even P <->
  Nat.modulo p 4 = 3.
Admitted.
