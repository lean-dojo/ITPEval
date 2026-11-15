(*
  Statement-only formalization of Hundred Theorems artifact 012,
  "The Independence of the Parallel Postulate". The Klein disk model
  satisfies Tarski's axioms 1-9 and 11 while refuting the Euclidean axiom 10.
  This file contains no proof.
*)

Require Import Reals.

Open Scope R_scope.

Definition R2 : Type := (R * R)%type.

Definition dot (u v : R2) : R :=
  fst u * fst v + snd u * snd v.

Definition norm_sq (u : R2) : R := dot u u.

(* The points of the Klein model are the points of the open unit disk. *)
Definition KleinPoint : Type := { u : R2 | norm_sq u < 1 }.

Definition coordinates (p : KleinPoint) : R2 := proj1_sig p.

Definition affine_combination (t : R) (u v : R2) : R2 :=
  ((1 - t) * fst u + t * fst v,
   (1 - t) * snd u + t * snd v).

Definition between (y x z : R2) : Prop :=
  exists t : R,
    0 <= t <= 1 /\ y = affine_combination t x z.

Definition pbetween (y x z : KleinPoint) : Prop :=
  between (coordinates y) (coordinates x) (coordinates z).

Definition ddist (u v : R2) : R :=
  ((1 - dot u v) * (1 - dot u v)) /
    ((1 - norm_sq u) * (1 - norm_sq v)) - 1.

Definition pdist (p q : KleinPoint) : R :=
  ddist (coordinates p) (coordinates q).

Definition pcongruent
    (a b c d : KleinPoint) : Prop :=
  pdist a b = pdist c d.

Definition tarski_axiom_1 : Prop :=
  forall a b : KleinPoint, pcongruent a b b a.

Definition tarski_axiom_2 : Prop :=
  forall a b p q r s : KleinPoint,
    pcongruent a b p q /\ pcongruent a b r s ->
    pcongruent p q r s.

Definition tarski_axiom_3 : Prop :=
  forall a b c : KleinPoint,
    pcongruent a b c c -> a = b.

Definition tarski_axiom_4 : Prop :=
  forall q a b c : KleinPoint,
    exists x : KleinPoint,
      pbetween a q x /\ pcongruent a x b c.

Definition tarski_axiom_5 : Prop :=
  forall a b c x a' b' c' x' : KleinPoint,
    a <> b /\
    pcongruent a b a' b' /\
    pcongruent a c a' c' /\
    pcongruent b c b' c' /\
    pbetween b a x /\
    pbetween b' a' x' /\
    pcongruent b x b' x' ->
    pcongruent c x c' x'.

Definition tarski_axiom_6 : Prop :=
  forall a b : KleinPoint,
    pbetween b a a -> a = b.

Definition tarski_axiom_7 : Prop :=
  forall a b c p q : KleinPoint,
    pbetween p a c /\ pbetween q b c ->
    exists x : KleinPoint,
      pbetween x p b /\ pbetween x q a.

Definition tarski_axiom_8 : Prop :=
  exists a b c : KleinPoint,
    ~ pbetween b a c /\
    ~ pbetween c b a /\
    ~ pbetween a c b.

Definition tarski_axiom_9 : Prop :=
  forall p q a b c : KleinPoint,
    p <> q /\
    pcongruent a p a q /\
    pcongruent b p b q /\
    pcongruent c p c q ->
    pbetween b a c \/ pbetween c b a \/ pbetween a c b.

Definition tarski_axiom_10 : Prop :=
  forall a b c d t : KleinPoint,
    pbetween d a t /\ pbetween d b c /\ a <> d ->
    exists x y : KleinPoint,
      pbetween b a x /\
      pbetween c a y /\
      pbetween t x y.

Definition tarski_axiom_11 : Prop :=
  forall X Y : KleinPoint -> Prop,
    (exists a : KleinPoint,
       forall x y : KleinPoint,
         X x /\ Y y -> pbetween x a y) ->
    exists b : KleinPoint,
      forall x y : KleinPoint,
        X x /\ Y y -> pbetween b x y.

Theorem klein_disc_independence_of_parallel_postulate :
  tarski_axiom_1 /\
  tarski_axiom_2 /\
  tarski_axiom_3 /\
  tarski_axiom_4 /\
  tarski_axiom_5 /\
  tarski_axiom_6 /\
  tarski_axiom_7 /\
  tarski_axiom_8 /\
  tarski_axiom_9 /\
  ~ tarski_axiom_10 /\
  tarski_axiom_11.
Proof.
Admitted.
