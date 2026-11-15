(* Statement-only formalization of PutnamBench corpus artifact putnam_2018_b5:
   a continuously differentiable map from the real plane to itself with
   positive partial derivatives and the stated pointwise derivative inequality
   is injective; this file contains no proof. *)

From Stdlib Require Import
  Reals
  ClassicalEpsilon.

Open Scope R_scope.

Definition putnam_2018_b5_vector : Type := (R * R)%type.

Definition putnam_2018_b5_real_derivative
    (g : R -> R) (x : R) : R :=
  epsilon (inhabits (0 : R))
    (fun d : R => derivable_pt_lim g x d).

Definition putnam_2018_b5_d11
    (f : putnam_2018_b5_vector -> putnam_2018_b5_vector)
    (p : putnam_2018_b5_vector) : R :=
  putnam_2018_b5_real_derivative
    (fun x : R => fst (f (x, snd p)))
    (fst p).

Definition putnam_2018_b5_d12
    (f : putnam_2018_b5_vector -> putnam_2018_b5_vector)
    (p : putnam_2018_b5_vector) : R :=
  putnam_2018_b5_real_derivative
    (fun y : R => fst (f (fst p, y)))
    (snd p).

Definition putnam_2018_b5_d21
    (f : putnam_2018_b5_vector -> putnam_2018_b5_vector)
    (p : putnam_2018_b5_vector) : R :=
  putnam_2018_b5_real_derivative
    (fun x : R => snd (f (x, snd p)))
    (fst p).

Definition putnam_2018_b5_d22
    (f : putnam_2018_b5_vector -> putnam_2018_b5_vector)
    (p : putnam_2018_b5_vector) : R :=
  putnam_2018_b5_real_derivative
    (fun y : R => snd (f (fst p, y)))
    (snd p).

Definition putnam_2018_b5_continuous_plane
    (g : putnam_2018_b5_vector -> R) : Prop :=
  forall p : putnam_2018_b5_vector,
    forall eps : R,
      eps > 0 ->
      exists delta : R,
        delta > 0 /\
        forall q : putnam_2018_b5_vector,
          Rabs (fst q - fst p) < delta ->
          Rabs (snd q - snd p) < delta ->
          Rabs (g q - g p) < eps.

Definition putnam_2018_b5_contdiff_one
    (f : putnam_2018_b5_vector -> putnam_2018_b5_vector) : Prop :=
  (forall p : putnam_2018_b5_vector,
    derivable_pt_lim
      (fun x : R => fst (f (x, snd p)))
      (fst p)
      (putnam_2018_b5_d11 f p) /\
    derivable_pt_lim
      (fun y : R => fst (f (fst p, y)))
      (snd p)
      (putnam_2018_b5_d12 f p) /\
    derivable_pt_lim
      (fun x : R => snd (f (x, snd p)))
      (fst p)
      (putnam_2018_b5_d21 f p) /\
    derivable_pt_lim
      (fun y : R => snd (f (fst p, y)))
      (snd p)
      (putnam_2018_b5_d22 f p)) /\
  putnam_2018_b5_continuous_plane (putnam_2018_b5_d11 f) /\
  putnam_2018_b5_continuous_plane (putnam_2018_b5_d12 f) /\
  putnam_2018_b5_continuous_plane (putnam_2018_b5_d21 f) /\
  putnam_2018_b5_continuous_plane (putnam_2018_b5_d22 f).

Theorem putnam_2018_b5
    (f : putnam_2018_b5_vector -> putnam_2018_b5_vector)
    (hf : putnam_2018_b5_contdiff_one f)
    (hpositive :
      forall p : putnam_2018_b5_vector,
        0 < putnam_2018_b5_d11 f p /\
        0 < putnam_2018_b5_d12 f p /\
        0 < putnam_2018_b5_d21 f p /\
        0 < putnam_2018_b5_d22 f p)
    (hinequality :
      forall p : putnam_2018_b5_vector,
        0 <
        putnam_2018_b5_d11 f p * putnam_2018_b5_d22 f p -
        (1 / 4) *
          (putnam_2018_b5_d12 f p + putnam_2018_b5_d21 f p) ^ 2) :
  forall p q : putnam_2018_b5_vector,
    f p = f q ->
    p = q.
Admitted.
