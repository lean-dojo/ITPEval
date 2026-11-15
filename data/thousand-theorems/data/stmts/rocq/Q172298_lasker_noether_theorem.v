(*
  Statement-only formalization of Thousand Theorems corpus artifact Q172298
  (thousand-theorems__rocq__Q172298), "Lasker–Noether theorem": a finite
  primary decomposition of a submodule can be replaced by one with the same
  intersection and pairwise distinct radicals of the corresponding colon
  ideals. This file contains no proof.
*)

From Stdlib Require Import List Arith.

Set Universe Polymorphism.
Set Implicit Arguments.

Record q172298_comm_semiring (R : Type) : Type := {
  q172298_ring_zero : R;
  q172298_ring_one : R;
  q172298_ring_add : R -> R -> R;
  q172298_ring_mul : R -> R -> R;
  q172298_ring_add_assoc :
    forall x y z : R,
      q172298_ring_add x (q172298_ring_add y z) =
      q172298_ring_add (q172298_ring_add x y) z;
  q172298_ring_add_comm :
    forall x y : R,
      q172298_ring_add x y = q172298_ring_add y x;
  q172298_ring_add_zero :
    forall x : R,
      q172298_ring_add x q172298_ring_zero = x;
  q172298_ring_mul_assoc :
    forall x y z : R,
      q172298_ring_mul x (q172298_ring_mul y z) =
      q172298_ring_mul (q172298_ring_mul x y) z;
  q172298_ring_mul_comm :
    forall x y : R,
      q172298_ring_mul x y = q172298_ring_mul y x;
  q172298_ring_mul_one :
    forall x : R,
      q172298_ring_mul x q172298_ring_one = x;
  q172298_ring_mul_zero :
    forall x : R,
      q172298_ring_mul x q172298_ring_zero = q172298_ring_zero;
  q172298_ring_mul_add :
    forall x y z : R,
      q172298_ring_mul x (q172298_ring_add y z) =
      q172298_ring_add
        (q172298_ring_mul x y) (q172298_ring_mul x z)
}.

Arguments q172298_ring_zero {R} _.
Arguments q172298_ring_one {R} _.
Arguments q172298_ring_add {R} _ _ _.
Arguments q172298_ring_mul {R} _ _ _.

Record q172298_add_comm_monoid (M : Type) : Type := {
  q172298_module_zero : M;
  q172298_module_add : M -> M -> M;
  q172298_module_add_assoc :
    forall x y z : M,
      q172298_module_add x (q172298_module_add y z) =
      q172298_module_add (q172298_module_add x y) z;
  q172298_module_add_comm :
    forall x y : M,
      q172298_module_add x y = q172298_module_add y x;
  q172298_module_add_zero :
    forall x : M,
      q172298_module_add x q172298_module_zero = x
}.

Arguments q172298_module_zero {M} _.
Arguments q172298_module_add {M} _ _ _.

Record q172298_module
    (R M : Type)
    (SR : q172298_comm_semiring R)
    (AM : q172298_add_comm_monoid M) : Type := {
  q172298_smul : R -> M -> M;
  q172298_one_smul :
    forall x : M,
      q172298_smul (q172298_ring_one SR) x = x;
  q172298_mul_smul :
    forall (a b : R) (x : M),
      q172298_smul (q172298_ring_mul SR a b) x =
      q172298_smul a (q172298_smul b x);
  q172298_smul_add :
    forall (a : R) (x y : M),
      q172298_smul a (q172298_module_add AM x y) =
      q172298_module_add AM (q172298_smul a x) (q172298_smul a y);
  q172298_add_smul :
    forall (a b : R) (x : M),
      q172298_smul (q172298_ring_add SR a b) x =
      q172298_module_add AM (q172298_smul a x) (q172298_smul b x);
  q172298_zero_smul :
    forall x : M,
      q172298_smul (q172298_ring_zero SR) x =
      q172298_module_zero AM;
  q172298_smul_zero :
    forall a : R,
      q172298_smul a (q172298_module_zero AM) =
      q172298_module_zero AM
}.

Arguments q172298_smul {R M SR AM} _ _ _.

Fixpoint q172298_pow
    {R : Type} (SR : q172298_comm_semiring R)
    (r : R) (n : nat) : R :=
  match n with
  | 0 => q172298_ring_one SR
  | S k => q172298_ring_mul SR r (q172298_pow SR r k)
  end.

Record q172298_submodule
    (R M : Type)
    (SR : q172298_comm_semiring R)
    (AM : q172298_add_comm_monoid M)
    (SM : q172298_module SR AM) : Type := {
  q172298_submodule_mem : M -> Prop;
  q172298_submodule_zero :
    q172298_submodule_mem (q172298_module_zero AM);
  q172298_submodule_add :
    forall x y : M,
      q172298_submodule_mem x ->
      q172298_submodule_mem y ->
      q172298_submodule_mem (q172298_module_add AM x y);
  q172298_submodule_smul :
    forall (r : R) (x : M),
      q172298_submodule_mem x ->
      q172298_submodule_mem (q172298_smul SM r x)
}.

Arguments q172298_submodule_mem {R M SR AM SM} _ _.

Definition q172298_submodule_equal
    {R M : Type}
    {SR : q172298_comm_semiring R}
    {AM : q172298_add_comm_monoid M}
    {SM : q172298_module SR AM}
    (N P : @q172298_submodule R M SR AM SM) : Prop :=
  forall x : M,
    q172298_submodule_mem N x <-> q172298_submodule_mem P x.

Definition q172298_submodule_in
    {R M : Type}
    {SR : q172298_comm_semiring R}
    {AM : q172298_add_comm_monoid M}
    {SM : q172298_module SR AM}
    (N : @q172298_submodule R M SR AM SM)
    (family : list (@q172298_submodule R M SR AM SM)) : Prop :=
  exists P : @q172298_submodule R M SR AM SM,
    In P family /\ q172298_submodule_equal N P.

Fixpoint q172298_submodule_nodup
    {R M : Type}
    {SR : q172298_comm_semiring R}
    {AM : q172298_add_comm_monoid M}
    {SM : q172298_module SR AM}
    (family : list (@q172298_submodule R M SR AM SM)) : Prop :=
  match family with
  | nil => True
  | N :: rest =>
      ~ q172298_submodule_in N rest /\
      q172298_submodule_nodup rest
  end.

Record q172298_finite_submodules
    (R M : Type)
    (SR : q172298_comm_semiring R)
    (AM : q172298_add_comm_monoid M)
    (SM : q172298_module SR AM) : Type := {
  q172298_elements : list (@q172298_submodule R M SR AM SM);
  q172298_elements_nodup :
    q172298_submodule_nodup q172298_elements
}.

Arguments q172298_elements {R M SR AM SM} _.

Definition q172298_infimum_equal
    {R M : Type}
    {SR : q172298_comm_semiring R}
    {AM : q172298_add_comm_monoid M}
    {SM : q172298_module SR AM}
    (family : @q172298_finite_submodules R M SR AM SM)
    (N : @q172298_submodule R M SR AM SM) : Prop :=
  forall x : M,
    q172298_submodule_mem N x <->
    forall P : @q172298_submodule R M SR AM SM,
      q172298_submodule_in P (q172298_elements family) ->
      q172298_submodule_mem P x.

Definition q172298_is_primary
    {R M : Type}
    {SR : q172298_comm_semiring R}
    {AM : q172298_add_comm_monoid M}
    {SM : q172298_module SR AM}
    (N : @q172298_submodule R M SR AM SM) : Prop :=
  ~ (forall x : M, q172298_submodule_mem N x) /\
  forall (r : R) (x : M),
    q172298_submodule_mem N (q172298_smul SM r x) ->
    q172298_submodule_mem N x \/
    exists n : nat,
      forall y : M,
        q172298_submodule_mem N
          (q172298_smul SM (q172298_pow SR r n) y).

Definition q172298_colon_radical_member
    {R M : Type}
    {SR : q172298_comm_semiring R}
    {AM : q172298_add_comm_monoid M}
    {SM : q172298_module SR AM}
    (N : @q172298_submodule R M SR AM SM)
    (r : R) : Prop :=
  exists n : nat,
    forall x : M,
      q172298_submodule_mem N
        (q172298_smul SM (q172298_pow SR r n) x).

Definition q172298_colon_radical_equal
    {R M : Type}
    {SR : q172298_comm_semiring R}
    {AM : q172298_add_comm_monoid M}
    {SM : q172298_module SR AM}
    (N P : @q172298_submodule R M SR AM SM) : Prop :=
  forall r : R,
    q172298_colon_radical_member N r <->
    q172298_colon_radical_member P r.

Definition q172298_pairwise_distinct_colon_radicals
    {R M : Type}
    {SR : q172298_comm_semiring R}
    {AM : q172298_add_comm_monoid M}
    {SM : q172298_module SR AM}
    (family : @q172298_finite_submodules R M SR AM SM) : Prop :=
  forall I J : @q172298_submodule R M SR AM SM,
    q172298_submodule_in I (q172298_elements family) ->
    q172298_submodule_in J (q172298_elements family) ->
    ~ q172298_submodule_equal I J ->
    ~ q172298_colon_radical_equal I J.

Theorem Ideal_isPrimary_decomposition_pairwise_ne_radical :
  forall (R M : Type)
         (SR : q172298_comm_semiring R)
         (AM : q172298_add_comm_monoid M)
         (SM : q172298_module SR AM)
         (N : @q172298_submodule R M SR AM SM)
         (s : @q172298_finite_submodules R M SR AM SM),
    q172298_infimum_equal s N ->
    (forall J : @q172298_submodule R M SR AM SM,
      q172298_submodule_in J (q172298_elements s) ->
      q172298_is_primary J) ->
    exists t : @q172298_finite_submodules R M SR AM SM,
      q172298_infimum_equal t N /\
      (forall J : @q172298_submodule R M SR AM SM,
        q172298_submodule_in J (q172298_elements t) ->
        q172298_is_primary J) /\
      q172298_pairwise_distinct_colon_radicals t.
Admitted.
