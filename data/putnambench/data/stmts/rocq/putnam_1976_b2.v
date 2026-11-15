(* Statement-only formalization of PutnamBench artifact putnam_1976_b2:
   determining all square elements in a two-generated group with specified
   relations. This file contains no proof. *)

From Stdlib Require Import Lists.List ZArith.ZArith.

Import ListNotations.

Record group_structure (G : Type) : Type := {
  group_mul : G -> G -> G;
  group_one : G;
  group_inv : G -> G;
  group_assoc :
    forall x y z : G,
      group_mul x (group_mul y z) = group_mul (group_mul x y) z;
  group_left_identity :
    forall x : G, group_mul group_one x = x;
  group_right_identity :
    forall x : G, group_mul x group_one = x;
  group_left_inverse :
    forall x : G, group_mul (group_inv x) x = group_one;
  group_right_inverse :
    forall x : G, group_mul x (group_inv x) = group_one
}.

Arguments group_mul {G} _ _ _.
Arguments group_one {G} _.
Arguments group_inv {G} _ _.

Fixpoint group_pow_nat
    {G : Type}
    (grp : group_structure G)
    (x : G)
    (n : nat) : G :=
  match n with
  | O => group_one grp
  | S k => group_mul grp x (group_pow_nat grp x k)
  end.

Definition group_zpow
    {G : Type}
    (grp : group_structure G)
    (x : G)
    (n : Z) : G :=
  match n with
  | Z0 => group_one grp
  | Zpos p => group_pow_nat grp x (Pos.to_nat p)
  | Zneg p => group_inv grp (group_pow_nat grp x (Pos.to_nat p))
  end.

Definition group_word
    {G : Type}
    (grp : group_structure G)
    (A B : G)
    (w : list (Z * Z)) : G :=
  fold_right
    (fun t acc =>
      group_mul grp
        (group_mul grp
          (group_zpow grp A (fst t))
          (group_zpow grp B (snd t)))
        acc)
    (group_one grp)
    w.

Definition putnam_1976_b2_solution : list (list (Z * Z)) :=
  [[(0%Z, 0%Z)];
   [(2%Z, 0%Z)];
   [(0%Z, 1%Z)];
   [(0%Z, 2%Z)];
   [(0%Z, 3%Z)];
   [(0%Z, 4%Z)];
   [(0%Z, 5%Z)];
   [(0%Z, 6%Z)]].

Theorem putnam_1976_b2
    (G : Type)
    (grp : group_structure G)
    (A B : G)
    (word : list (Z * Z) -> G)
    (hword : word = group_word grp A B)
    (hG : forall g : G, exists w : list (Z * Z), g = word w)
    (hA :
      group_pow_nat grp A 4 = group_one grp /\
      group_pow_nat grp A 2 <> group_one grp)
    (hB :
      group_pow_nat grp B 7 = group_one grp /\
      B <> group_one grp)
    (h1 :
      group_mul grp
        (group_mul grp
          (group_mul grp A B)
          (group_inv grp A))
        B =
      group_one grp)
    (S : G -> Prop)
    (hS :
      forall g : G,
        S g <-> exists C : G, group_mul grp C C = g) :
  NoDup (map word putnam_1976_b2_solution) /\
  forall g : G,
    S g <-> In g (map word putnam_1976_b2_solution).
Admitted.
