(* Statement-only formalization of PutnamBench corpus artifact putnam_2008_a6:
   a universal logarithmic-length sequence whose subsequence products cover
   every element of each nontrivial finite group. This file contains no proof. *)

From Stdlib Require Import Reals Lists.List.

Open Scope R_scope.

Record putnam_2008_a6_group (G : Type) : Type := {
  putnam_2008_a6_mul : G -> G -> G;
  putnam_2008_a6_one : G;
  putnam_2008_a6_inv : G -> G;
  putnam_2008_a6_assoc :
    forall x y z : G,
      putnam_2008_a6_mul x (putnam_2008_a6_mul y z) =
      putnam_2008_a6_mul (putnam_2008_a6_mul x y) z;
  putnam_2008_a6_left_identity :
    forall x : G, putnam_2008_a6_mul putnam_2008_a6_one x = x;
  putnam_2008_a6_right_identity :
    forall x : G, putnam_2008_a6_mul x putnam_2008_a6_one = x;
  putnam_2008_a6_left_inverse :
    forall x : G,
      putnam_2008_a6_mul (putnam_2008_a6_inv x) x =
      putnam_2008_a6_one;
  putnam_2008_a6_right_inverse :
    forall x : G,
      putnam_2008_a6_mul x (putnam_2008_a6_inv x) =
      putnam_2008_a6_one
}.

Arguments putnam_2008_a6_mul {G} _ _ _.
Arguments putnam_2008_a6_one {G} _.

Inductive putnam_2008_a6_subsequence {G : Type} :
    list G -> list G -> Prop :=
  | putnam_2008_a6_subsequence_nil :
      putnam_2008_a6_subsequence nil nil
  | putnam_2008_a6_subsequence_skip :
      forall (x : G) (selected source : list G),
        putnam_2008_a6_subsequence selected source ->
        putnam_2008_a6_subsequence selected (x :: source)
  | putnam_2008_a6_subsequence_take :
      forall (x : G) (selected source : list G),
        putnam_2008_a6_subsequence selected source ->
        putnam_2008_a6_subsequence
          (x :: selected) (x :: source).

Definition putnam_2008_a6_product
    {G : Type}
    (grp : putnam_2008_a6_group G)
    (xs : list G) : G :=
  fold_right
    (putnam_2008_a6_mul grp)
    (putnam_2008_a6_one grp)
    xs.

Theorem putnam_2008_a6 :
  exists c : R,
    0 < c /\
    forall
      (G : Type)
      (grp : putnam_2008_a6_group G)
      (enumeration : list G),
      NoDup enumeration ->
      (forall g : G, In g enumeration) ->
      (1 < length enumeration)%nat ->
      exists s : list G,
        INR (length s) <= c * ln (INR (length enumeration)) /\
        forall g : G,
          exists t : list G,
            putnam_2008_a6_subsequence t s /\
            putnam_2008_a6_product grp t = g.
Admitted.
