(*
  Statement-only formalization of "Descartes Rule of Signs" from Hundred
  Theorems artifact 100: coefficient sign variations equal the number of
  positive real roots counted with multiplicity plus an even number. This
  file contains no proof.
*)

From Stdlib Require Import Reals List Bool Arith.

Import ListNotations.
Open Scope R_scope.

Definition polynomial := list R.

Fixpoint poly_eval (p : polynomial) (x : R) : R :=
  match p with
  | [] => 0
  | a :: q => a + x * poly_eval q x
  end.

Definition polynomial_nonzero (p : polynomial) : Prop :=
  exists a : R, In a p /\ a <> 0.

Fixpoint poly_derivative_aux (p : polynomial) (n : nat) : polynomial :=
  match p with
  | [] => []
  | a :: q => INR n * a :: poly_derivative_aux q (S n)
  end.

Definition poly_derivative (p : polynomial) : polynomial :=
  match p with
  | [] => []
  | _ :: q => poly_derivative_aux q 1%nat
  end.

Fixpoint iter_derivative (n : nat) (p : polynomial) : polynomial :=
  match n with
  | O => p
  | S k => poly_derivative (iter_derivative k p)
  end.

Definition root_multiplicity
    (p : polynomial) (r : R) (m : nat) : Prop :=
  (forall k : nat, (k < m)%nat ->
    poly_eval (iter_derivative k p) r = 0) /\
  poly_eval (iter_derivative m p) r <> 0.

Definition coefficient_sign (x : R) : option bool :=
  if Rlt_dec 0 x then Some true
  else if Rlt_dec x 0 then Some false
  else None.

Fixpoint sign_variations_from
    (previous : option bool) (coefficients : polynomial) : nat :=
  match coefficients with
  | [] => O
  | a :: q =>
      match coefficient_sign a with
      | None => sign_variations_from previous q
      | Some current =>
          let rest := sign_variations_from (Some current) q in
          match previous with
          | None => rest
          | Some old =>
              if Bool.eqb old current then rest else S rest
          end
      end
  end.

Definition sign_variations (p : polynomial) : nat :=
  sign_variations_from None p.

Definition root_entry := (R * nat)%type.

Fixpoint total_multiplicity (roots : list root_entry) : nat :=
  match roots with
  | [] => O
  | (_, m) :: rest => (m + total_multiplicity rest)%nat
  end.

Definition positive_root_data
    (p : polynomial) (roots : list root_entry) : Prop :=
  NoDup (map (@fst R nat) roots) /\
  (forall (r : R) (m : nat),
    In (r, m) roots -> root_multiplicity p r m) /\
  (forall r : R,
    (0 < r /\ poly_eval p r = 0) <->
    exists m : nat, In (r, m) roots).

Definition even_nat (n : nat) : Prop :=
  exists k : nat, n = (2 * k)%nat.

Theorem descartes_rule_of_signs :
  forall p : polynomial,
    polynomial_nonzero p ->
    exists roots : list root_entry,
      exists d : nat,
        positive_root_data p roots /\
        even_nat d /\
        sign_variations p = (total_multiplicity roots + d)%nat.
Admitted.
