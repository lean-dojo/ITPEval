(*
  Statement-only formalization of Thousand Theorems corpus artifact Q7888360
  (thousand-theorems__rocq__Q7888360), "Structure theorem for finitely
  generated modules over a principal ideal domain": every finitely generated
  module over a principal ideal domain is linearly isomorphic to a finite-rank
  free module times a finite direct sum of cyclic prime-power quotients. This
  file contains no proof.
*)

From Stdlib Require Import List Vectors.Fin.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.

Record q7888360_commutative_ring (R : Type) : Type := {
  q7888360_zero : R;
  q7888360_one : R;
  q7888360_add : R -> R -> R;
  q7888360_mul : R -> R -> R;
  q7888360_neg : R -> R;
  q7888360_add_assoc :
    forall x y z : R,
      q7888360_add x (q7888360_add y z) =
      q7888360_add (q7888360_add x y) z;
  q7888360_add_comm :
    forall x y : R,
      q7888360_add x y = q7888360_add y x;
  q7888360_zero_add :
    forall x : R, q7888360_add q7888360_zero x = x;
  q7888360_add_zero :
    forall x : R, q7888360_add x q7888360_zero = x;
  q7888360_neg_add :
    forall x : R,
      q7888360_add (q7888360_neg x) x = q7888360_zero;
  q7888360_add_neg :
    forall x : R,
      q7888360_add x (q7888360_neg x) = q7888360_zero;
  q7888360_mul_assoc :
    forall x y z : R,
      q7888360_mul x (q7888360_mul y z) =
      q7888360_mul (q7888360_mul x y) z;
  q7888360_mul_comm :
    forall x y : R,
      q7888360_mul x y = q7888360_mul y x;
  q7888360_one_mul :
    forall x : R, q7888360_mul q7888360_one x = x;
  q7888360_mul_one :
    forall x : R, q7888360_mul x q7888360_one = x;
  q7888360_mul_add :
    forall x y z : R,
      q7888360_mul x (q7888360_add y z) =
      q7888360_add
        (q7888360_mul x y) (q7888360_mul x z);
  q7888360_add_mul :
    forall x y z : R,
      q7888360_mul (q7888360_add x y) z =
      q7888360_add
        (q7888360_mul x z) (q7888360_mul y z)
}.

Arguments q7888360_zero {R} _.
Arguments q7888360_one {R} _.
Arguments q7888360_add {R} _ _ _.
Arguments q7888360_mul {R} _ _ _.
Arguments q7888360_neg {R} _ _.

Record q7888360_integral_domain
    {R : Type}
    (CR : q7888360_commutative_ring R) : Prop := {
  q7888360_zero_ne_one :
    q7888360_zero CR <> q7888360_one CR;
  q7888360_mul_eq_zero :
    forall x y : R,
      q7888360_mul CR x y = q7888360_zero CR ->
      x = q7888360_zero CR \/ y = q7888360_zero CR
}.

Record q7888360_ideal
    {R : Type}
    (CR : q7888360_commutative_ring R) : Type := {
  q7888360_ideal_mem : R -> Prop;
  q7888360_ideal_zero :
    q7888360_ideal_mem (q7888360_zero CR);
  q7888360_ideal_add :
    forall x y : R,
      q7888360_ideal_mem x ->
      q7888360_ideal_mem y ->
      q7888360_ideal_mem (q7888360_add CR x y);
  q7888360_ideal_neg :
    forall x : R,
      q7888360_ideal_mem x ->
      q7888360_ideal_mem (q7888360_neg CR x);
  q7888360_ideal_mul :
    forall a x : R,
      q7888360_ideal_mem x ->
      q7888360_ideal_mem (q7888360_mul CR a x)
}.

Arguments q7888360_ideal_mem {R CR} _ _.

Record q7888360_principal_ideal_ring
    {R : Type}
    (CR : q7888360_commutative_ring R) : Prop := {
  q7888360_every_ideal_principal :
    forall I : q7888360_ideal CR,
      exists generator : R,
        forall x : R,
          q7888360_ideal_mem I x <->
          exists coefficient : R,
            x = q7888360_mul CR coefficient generator
}.

Record q7888360_module
    {R M : Type}
    (CR : q7888360_commutative_ring R) : Type := {
  q7888360_mzero : M;
  q7888360_madd : M -> M -> M;
  q7888360_mneg : M -> M;
  q7888360_smul : R -> M -> M;
  q7888360_madd_assoc :
    forall x y z : M,
      q7888360_madd x (q7888360_madd y z) =
      q7888360_madd (q7888360_madd x y) z;
  q7888360_madd_comm :
    forall x y : M,
      q7888360_madd x y = q7888360_madd y x;
  q7888360_mzero_add :
    forall x : M, q7888360_madd q7888360_mzero x = x;
  q7888360_madd_zero :
    forall x : M, q7888360_madd x q7888360_mzero = x;
  q7888360_mneg_add :
    forall x : M,
      q7888360_madd (q7888360_mneg x) x = q7888360_mzero;
  q7888360_madd_neg :
    forall x : M,
      q7888360_madd x (q7888360_mneg x) = q7888360_mzero;
  q7888360_one_smul :
    forall x : M,
      q7888360_smul (q7888360_one CR) x = x;
  q7888360_mul_smul :
    forall (r s : R) (x : M),
      q7888360_smul (q7888360_mul CR r s) x =
      q7888360_smul r (q7888360_smul s x);
  q7888360_add_smul :
    forall (r s : R) (x : M),
      q7888360_smul (q7888360_add CR r s) x =
      q7888360_madd
        (q7888360_smul r x) (q7888360_smul s x);
  q7888360_smul_add :
    forall (r : R) (x y : M),
      q7888360_smul r (q7888360_madd x y) =
      q7888360_madd
        (q7888360_smul r x) (q7888360_smul r y);
  q7888360_zero_smul :
    forall x : M,
      q7888360_smul (q7888360_zero CR) x = q7888360_mzero;
  q7888360_smul_zero :
    forall r : R,
      q7888360_smul r q7888360_mzero = q7888360_mzero
}.

Arguments q7888360_mzero {R M CR} _.
Arguments q7888360_madd {R M CR} _ _ _.
Arguments q7888360_mneg {R M CR} _ _.
Arguments q7888360_smul {R M CR} _ _ _.

Fixpoint q7888360_linear_combination
    {R M : Type}
    {CR : q7888360_commutative_ring R}
    (SM : @q7888360_module R M CR)
    (coefficients : list R)
    (generators : list M) : M :=
  match coefficients, generators with
  | coefficient :: coefficient_rest, generator :: generator_rest =>
      q7888360_madd SM
        (q7888360_smul SM coefficient generator)
        (q7888360_linear_combination
          SM coefficient_rest generator_rest)
  | _, _ => q7888360_mzero SM
  end.

Definition q7888360_finitely_generated
    {R M : Type}
    {CR : q7888360_commutative_ring R}
    (SM : @q7888360_module R M CR) : Prop :=
  exists generators : list M,
    forall x : M,
      exists coefficients : list R,
        length coefficients = length generators /\
        x = q7888360_linear_combination SM coefficients generators.

Fixpoint q7888360_pow
    {R : Type}
    (CR : q7888360_commutative_ring R)
    (x : R) (n : nat) : R :=
  match n with
  | 0 => q7888360_one CR
  | S k => q7888360_mul CR x (q7888360_pow CR x k)
  end.

Definition q7888360_is_unit
    {R : Type}
    {CR : q7888360_commutative_ring R}
    (x : R) : Prop :=
  exists inverse : R,
    q7888360_mul CR x inverse = q7888360_one CR /\
    q7888360_mul CR inverse x = q7888360_one CR.

Definition q7888360_irreducible
    {R : Type}
    {CR : q7888360_commutative_ring R}
    (x : R) : Prop :=
  ~ @q7888360_is_unit R CR x /\
  forall a b : R,
    x = q7888360_mul CR a b ->
    @q7888360_is_unit R CR a \/ @q7888360_is_unit R CR b.

Record q7888360_finite_type (I : Type) : Type := {
  q7888360_enumeration : list I;
  q7888360_enumeration_nodup :
    NoDup q7888360_enumeration;
  q7888360_enumeration_complete :
    forall i : I, In i q7888360_enumeration
}.

Definition q7888360_target_carrier
    (R I : Type) (n : nat) : Type :=
  ((Fin.t n -> R) * (I -> R))%type.

Definition q7888360_target_equiv
    {R I : Type}
    (CR : q7888360_commutative_ring R)
    (n : nat)
    (p : I -> R)
    (e : I -> nat)
    (x y : q7888360_target_carrier R I n) : Prop :=
  (forall j : Fin.t n, fst x j = fst y j) /\
  (forall i : I,
    exists coefficient : R,
      snd x i =
      q7888360_add CR
        (snd y i)
        (q7888360_mul CR coefficient
          (q7888360_pow CR (p i) (e i)))).

Definition q7888360_target_add
    {R I : Type}
    (CR : q7888360_commutative_ring R)
    (n : nat)
    (x y : q7888360_target_carrier R I n) :
    q7888360_target_carrier R I n :=
  (fun j => q7888360_add CR (fst x j) (fst y j),
   fun i => q7888360_add CR (snd x i) (snd y i)).

Definition q7888360_target_smul
    {R I : Type}
    (CR : q7888360_commutative_ring R)
    (n : nat)
    (r : R)
    (x : q7888360_target_carrier R I n) :
    q7888360_target_carrier R I n :=
  (fun j => q7888360_mul CR r (fst x j),
   fun i => q7888360_mul CR r (snd x i)).

Record q7888360_linear_equiv_decomposition
    {R M I : Type}
    {CR : q7888360_commutative_ring R}
    (SM : @q7888360_module R M CR)
    (n : nat)
    (p : I -> R)
    (e : I -> nat) : Type := {
  q7888360_forward :
    M -> q7888360_target_carrier R I n;
  q7888360_backward :
    q7888360_target_carrier R I n -> M;
  q7888360_backward_respects :
    forall x y : q7888360_target_carrier R I n,
      @q7888360_target_equiv R I CR n p e x y ->
      q7888360_backward x = q7888360_backward y;
  q7888360_left_inverse :
    forall x : M,
      q7888360_backward (q7888360_forward x) = x;
  q7888360_right_inverse :
    forall y : q7888360_target_carrier R I n,
      @q7888360_target_equiv R I CR n p e
        (q7888360_forward (q7888360_backward y)) y;
  q7888360_forward_add :
    forall x y : M,
      @q7888360_target_equiv R I CR n p e
        (q7888360_forward (q7888360_madd SM x y))
        (@q7888360_target_add R I CR n
          (q7888360_forward x) (q7888360_forward y));
  q7888360_forward_smul :
    forall (r : R) (x : M),
      @q7888360_target_equiv R I CR n p e
        (q7888360_forward (q7888360_smul SM r x))
        (@q7888360_target_smul R I CR n r (q7888360_forward x))
}.

Theorem Module_equiv_free_prod_directSum :
  forall (R M : Type)
         (CR : q7888360_commutative_ring R)
         (PID : q7888360_principal_ideal_ring CR)
         (domain : q7888360_integral_domain CR)
         (SM : @q7888360_module R M CR),
    q7888360_finitely_generated SM ->
    exists (n : nat)
           (I : Type)
           (finite_I : q7888360_finite_type I)
           (p : I -> R)
           (e : I -> nat),
      (forall i : I, @q7888360_irreducible R CR (p i)) /\
      exists equivalence :
        @q7888360_linear_equiv_decomposition
          R M I CR SM n p e,
        True.
Admitted.
