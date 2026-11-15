(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1227702
  (thousand-theorems__rocq__Q1227702), "Dirichlet's unit theorem": for a
  number field, the unit group of its ring of integers modulo torsion has a
  finite integer basis, and every unit has a unique decomposition as a root
  of unity times integer powers of corresponding fundamental units.
  This file contains no proof.
*)

From Stdlib Require Import
  Arith.PeanoNat Lists.List QArith.QArith Reals
  Vectors.Fin ZArith.ZArith.

Set Universe Polymorphism.
Set Implicit Arguments.

Record q1227702_field (K : Type) : Type := {
  q1227702_zero : K;
  q1227702_one : K;
  q1227702_add : K -> K -> K;
  q1227702_mul : K -> K -> K;
  q1227702_neg : K -> K;
  q1227702_inv : K -> K;
  q1227702_add_assoc :
    forall x y z : K,
      q1227702_add x (q1227702_add y z) =
      q1227702_add (q1227702_add x y) z;
  q1227702_add_comm :
    forall x y : K, q1227702_add x y = q1227702_add y x;
  q1227702_add_zero :
    forall x : K, q1227702_add x q1227702_zero = x;
  q1227702_add_neg :
    forall x : K,
      q1227702_add x (q1227702_neg x) = q1227702_zero;
  q1227702_mul_assoc :
    forall x y z : K,
      q1227702_mul x (q1227702_mul y z) =
      q1227702_mul (q1227702_mul x y) z;
  q1227702_mul_comm :
    forall x y : K, q1227702_mul x y = q1227702_mul y x;
  q1227702_mul_one :
    forall x : K, q1227702_mul x q1227702_one = x;
  q1227702_left_distrib :
    forall x y z : K,
      q1227702_mul x (q1227702_add y z) =
      q1227702_add
        (q1227702_mul x y) (q1227702_mul x z);
  q1227702_mul_inv :
    forall x : K,
      x <> q1227702_zero ->
      q1227702_mul x (q1227702_inv x) = q1227702_one;
  q1227702_nontrivial : q1227702_zero <> q1227702_one
}.

Arguments q1227702_zero {K} _.
Arguments q1227702_one {K} _.
Arguments q1227702_add {K} _ _ _.
Arguments q1227702_mul {K} _ _ _.
Arguments q1227702_neg {K} _ _.
Arguments q1227702_inv {K} _ _.

Fixpoint q1227702_vector_sum
    {K : Type}
    (FK : q1227702_field K)
    (n : nat) : (Fin.t n -> K) -> K :=
  match n as m return (Fin.t m -> K) -> K with
  | O => fun _ => q1227702_zero FK
  | S m =>
      fun terms =>
        q1227702_add FK
          (terms Fin.F1)
          (@q1227702_vector_sum K FK m
            (fun i => terms (Fin.FS i)))
  end.

Arguments q1227702_vector_sum {K} FK n _.

Record q1227702_number_field
    (K : Type) (FK : q1227702_field K) : Type := {
  q1227702_q_smul : Q -> K -> K;
  q1227702_q_smul_one :
    forall x : K, q1227702_q_smul 1%Q x = x;
  q1227702_q_smul_assoc :
    forall (a b : Q) (x : K),
      q1227702_q_smul (a * b)%Q x =
      q1227702_q_smul a (q1227702_q_smul b x);
  q1227702_q_add_smul :
    forall (a b : Q) (x : K),
      q1227702_q_smul (a + b)%Q x =
      q1227702_add FK
        (q1227702_q_smul a x) (q1227702_q_smul b x);
  q1227702_q_smul_add :
    forall (a : Q) (x y : K),
      q1227702_q_smul a (q1227702_add FK x y) =
      q1227702_add FK
        (q1227702_q_smul a x) (q1227702_q_smul a y);
  q1227702_q_smul_mul :
    forall (a : Q) (x y : K),
      q1227702_q_smul a (q1227702_mul FK x y) =
      q1227702_mul FK (q1227702_q_smul a x) y;
  q1227702_q_embedding_injective :
    forall a b : Q,
      q1227702_q_smul a (q1227702_one FK) =
      q1227702_q_smul b (q1227702_one FK) ->
      a = b;
  q1227702_dimension : nat;
  q1227702_basis : Fin.t q1227702_dimension -> K;
  q1227702_basis_spans :
    forall x : K,
      exists coefficients : Fin.t q1227702_dimension -> Q,
        x =
        q1227702_vector_sum FK q1227702_dimension
          (fun i =>
            q1227702_q_smul
              (coefficients i) (q1227702_basis i));
  q1227702_basis_independent :
    forall coefficients : Fin.t q1227702_dimension -> Q,
      q1227702_vector_sum FK q1227702_dimension
        (fun i =>
          q1227702_q_smul
            (coefficients i) (q1227702_basis i)) =
      q1227702_zero FK ->
      forall i : Fin.t q1227702_dimension,
        coefficients i = 0%Q
}.

Arguments q1227702_q_smul {K FK} _ _ _.
Arguments q1227702_dimension {K FK} _.

Definition q1227702_integer_embedding
    {K : Type}
    {FK : q1227702_field K}
    (NF : q1227702_number_field FK)
    (z : Z) : K :=
  q1227702_q_smul NF (inject_Z z) (q1227702_one FK).

Fixpoint q1227702_integer_polynomial_eval
    {K : Type}
    {FK : q1227702_field K}
    (NF : q1227702_number_field FK)
    (coefficients : list Z)
    (x : K) : K :=
  match coefficients with
  | nil => q1227702_zero FK
  | z :: rest =>
      q1227702_add FK
        (q1227702_integer_embedding NF z)
        (q1227702_mul FK x
          (q1227702_integer_polynomial_eval NF rest x))
  end.

Definition q1227702_is_algebraic_integer
    {K : Type}
    {FK : q1227702_field K}
    (NF : q1227702_number_field FK)
    (x : K) : Prop :=
  exists coefficients : list Z,
    coefficients <> nil /\
    List.last coefficients 0%Z = 1%Z /\
    q1227702_integer_polynomial_eval NF coefficients x =
      q1227702_zero FK.

Definition q1227702_is_integer_unit
    {K : Type}
    {FK : q1227702_field K}
    (NF : q1227702_number_field FK)
    (x : K) : Prop :=
  q1227702_is_algebraic_integer NF x /\
  exists y : K,
    q1227702_is_algebraic_integer NF y /\
    q1227702_mul FK x y = q1227702_one FK.

Fixpoint q1227702_nat_pow
    {K : Type}
    (FK : q1227702_field K)
    (x : K)
    (n : nat) : K :=
  match n with
  | O => q1227702_one FK
  | S m =>
      q1227702_mul FK x (q1227702_nat_pow FK x m)
  end.

Definition q1227702_zpow
    {K : Type}
    (FK : q1227702_field K)
    (x : K)
    (z : Z) : K :=
  match z with
  | Z0 => q1227702_one FK
  | Zpos p =>
      q1227702_nat_pow FK x (Pos.to_nat p)
  | Zneg p =>
      q1227702_inv FK
        (q1227702_nat_pow FK x (Pos.to_nat p))
  end.

Fixpoint q1227702_product
    {K : Type}
    (FK : q1227702_field K)
    (n : nat) : (Fin.t n -> K) -> K :=
  match n as m return (Fin.t m -> K) -> K with
  | O => fun _ => q1227702_one FK
  | S m =>
      fun terms =>
        q1227702_mul FK
          (terms Fin.F1)
          (@q1227702_product K FK m
            (fun i => terms (Fin.FS i)))
  end.

Arguments q1227702_product {K} FK n _.

Definition q1227702_complex : Type :=
  (RbaseSymbolsImpl.R * RbaseSymbolsImpl.R)%type.

Definition q1227702_complex_zero : q1227702_complex := (0%R, 0%R).

Definition q1227702_complex_one : q1227702_complex := (1%R, 0%R).

Definition q1227702_complex_add
    (z w : q1227702_complex) : q1227702_complex :=
  ((fst z + fst w)%R, (snd z + snd w)%R).

Definition q1227702_complex_mul
    (z w : q1227702_complex) : q1227702_complex :=
  ((fst z * fst w - snd z * snd w)%R,
   (fst z * snd w + snd z * fst w)%R).

Definition q1227702_complex_conj
    (z : q1227702_complex) : q1227702_complex :=
  (fst z, (- snd z)%R).

Definition q1227702_is_complex_embedding
    {K : Type}
    (FK : q1227702_field K)
    (embedding : K -> q1227702_complex) : Prop :=
  embedding (q1227702_zero FK) = q1227702_complex_zero /\
  embedding (q1227702_one FK) = q1227702_complex_one /\
  (forall x y : K,
    embedding (q1227702_add FK x y) =
    q1227702_complex_add (embedding x) (embedding y)) /\
  forall x y : K,
    embedding (q1227702_mul FK x y) =
    q1227702_complex_mul (embedding x) (embedding y).

Definition q1227702_embeddings_conjugate
    {K : Type}
    (left right : K -> q1227702_complex) : Prop :=
  (forall x : K, left x = right x) \/
  forall x : K,
    left x = q1227702_complex_conj (right x).

Record q1227702_archimedean_places
    {K : Type}
    (FK : q1227702_field K) : Type := {
  q1227702_place_count : nat;
  q1227702_place_representative :
    Fin.t q1227702_place_count -> K -> q1227702_complex;
  q1227702_place_valid :
    forall i : Fin.t q1227702_place_count,
      q1227702_is_complex_embedding FK
        (q1227702_place_representative i);
  q1227702_place_separated :
    forall i j : Fin.t q1227702_place_count,
      q1227702_embeddings_conjugate
        (q1227702_place_representative i)
        (q1227702_place_representative j) ->
      i = j;
  q1227702_place_complete :
    forall embedding : K -> q1227702_complex,
      q1227702_is_complex_embedding FK embedding ->
      exists i : Fin.t q1227702_place_count,
        q1227702_embeddings_conjugate
          embedding (q1227702_place_representative i);
  q1227702_place_nonempty : (0 < q1227702_place_count)%nat
}.

Arguments q1227702_place_count {K FK} _.

Definition q1227702_unit_rank
    {K : Type}
    {FK : q1227702_field K}
    (places : q1227702_archimedean_places FK) : nat :=
  (q1227702_place_count places - 1)%nat.

Definition q1227702_is_torsion_unit
    {K : Type}
    {FK : q1227702_field K}
    (NF : q1227702_number_field FK)
    (x : K) : Prop :=
  q1227702_is_integer_unit NF x /\
  exists n : nat,
    (0 < n)%nat /\
    q1227702_nat_pow FK x n = q1227702_one FK.

Definition q1227702_same_mod_torsion
    {K : Type}
    {FK : q1227702_field K}
    (NF : q1227702_number_field FK)
    (x y : K) : Prop :=
  q1227702_is_integer_unit NF x /\
  q1227702_is_integer_unit NF y /\
  q1227702_is_torsion_unit NF
    (q1227702_mul FK x (q1227702_inv FK y)).

Definition q1227702_fundamental_product
    {K : Type}
    {FK : q1227702_field K}
    {rank : nat}
    (fundamental_units : Fin.t rank -> K)
    (exponents : Fin.t rank -> Z) : K :=
  q1227702_product FK rank
    (fun i =>
      q1227702_zpow FK
        (fundamental_units i) (exponents i)).

Record q1227702_basis_mod_torsion
    {K : Type}
    {FK : q1227702_field K}
    (NF : q1227702_number_field FK)
    (rank : nat) : Type := {
  q1227702_fundamental_units : Fin.t rank -> K;
  q1227702_fundamental_units_are_units :
    forall i : Fin.t rank,
      q1227702_is_integer_unit NF
        (q1227702_fundamental_units i);
  q1227702_basis_spans_mod_torsion :
    forall x : K,
      q1227702_is_integer_unit NF x ->
      exists exponents : Fin.t rank -> Z,
        q1227702_same_mod_torsion NF x
          (@q1227702_fundamental_product K FK rank
            q1227702_fundamental_units exponents);
  q1227702_basis_independent_mod_torsion :
    forall exponents : Fin.t rank -> Z,
      q1227702_same_mod_torsion NF
        (@q1227702_fundamental_product K FK rank
          q1227702_fundamental_units exponents)
        (q1227702_one FK) ->
      forall i : Fin.t rank, exponents i = 0%Z
}.

Definition NumberField_Units_basisModTorsion
    {K : Type}
    {FK : q1227702_field K}
    (NF : q1227702_number_field FK)
    (rank : nat) : Type :=
  q1227702_basis_mod_torsion NF rank.

Definition q1227702_is_unit_decomposition
    {K : Type}
    {FK : q1227702_field K}
    {rank : nat}
    (NF : q1227702_number_field FK)
    (basis : NumberField_Units_basisModTorsion NF rank)
    (x torsion_factor : K)
    (exponents : Fin.t rank -> Z) : Prop :=
  q1227702_is_torsion_unit NF torsion_factor /\
  x =
  q1227702_mul FK torsion_factor
    (@q1227702_fundamental_product K FK rank
      (q1227702_fundamental_units basis) exponents).

Theorem NumberField_Units_exist_unique_eq_mul_prod :
  forall (K : Type)
         (FK : q1227702_field K)
         (NF : q1227702_number_field FK),
    exists places : q1227702_archimedean_places FK,
      exists basis :
        NumberField_Units_basisModTorsion NF
          (q1227702_unit_rank places),
        forall x : K,
          q1227702_is_integer_unit NF x ->
          exists (torsion_factor : K)
                 (exponents :
                   Fin.t (q1227702_unit_rank places) -> Z),
            @q1227702_is_unit_decomposition
              K FK (q1227702_unit_rank places)
              NF basis x torsion_factor exponents /\
            forall (other_torsion_factor : K)
                   (other_exponents :
                     Fin.t (q1227702_unit_rank places) -> Z),
              @q1227702_is_unit_decomposition
                K FK (q1227702_unit_rank places)
                NF basis x other_torsion_factor other_exponents ->
              other_torsion_factor = torsion_factor /\
              forall i : Fin.t (q1227702_unit_rank places),
                other_exponents i = exponents i.
Admitted.
