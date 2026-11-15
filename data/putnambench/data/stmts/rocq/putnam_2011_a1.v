(* Statement-only formalization of PutnamBench corpus artifact putnam_2011_a1:
   counting points with integer coordinates from 0 through 2011 that cannot
   be endpoints of a growing axis-aligned spiral. This file contains no proof. *)

From Stdlib Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition putnam_2011_a1_point : Type := (Z * Z)%type.

Inductive putnam_2011_a1_direction : Type :=
  | East
  | North
  | West
  | South.

Definition putnam_2011_a1_next_direction
    (direction : putnam_2011_a1_direction)
    : putnam_2011_a1_direction :=
  match direction with
  | East => North
  | North => West
  | West => South
  | South => East
  end.

Definition putnam_2011_a1_step
    (direction : putnam_2011_a1_direction)
    (p q : putnam_2011_a1_point)
    (distance : nat) : Prop :=
  let d := Z.of_nat distance in
  match direction with
  | East =>
      fst q = fst p + d /\ snd q = snd p
  | North =>
      fst q = fst p /\ snd q = snd p + d
  | West =>
      fst q = fst p - d /\ snd q = snd p
  | South =>
      fst q = fst p /\ snd q = snd p - d
  end.

Fixpoint putnam_2011_a1_strictly_increasing
    (distances : list nat) : Prop :=
  match distances with
  | [] => True
  | distance :: remaining =>
      Forall (fun later => (distance < later)%nat) remaining /\
      putnam_2011_a1_strictly_increasing remaining
  end.

Fixpoint putnam_2011_a1_follows_directions
    (direction : putnam_2011_a1_direction)
    (points : list putnam_2011_a1_point)
    (distances : list nat) : Prop :=
  match points with
  | [] => False
  | p :: remaining_points =>
      match remaining_points, distances with
      | [], [] => True
      | q :: later_points, distance :: later_distances =>
          putnam_2011_a1_step direction p q distance /\
          putnam_2011_a1_follows_directions
            (putnam_2011_a1_next_direction direction)
            (q :: later_points)
            later_distances
      | _, _ => False
      end
  end.

Definition putnam_2011_a1_is_spiral
    (points : list putnam_2011_a1_point) : Prop :=
  (3 <= length points)%nat /\
  hd_error points = Some (0%Z, 0%Z) /\
  exists distances : list nat,
    Forall (fun distance => (0 < distance)%nat) distances /\
    putnam_2011_a1_strictly_increasing distances /\
    putnam_2011_a1_follows_directions East points distances.

Definition putnam_2011_a1_ends_at
    (points : list putnam_2011_a1_point)
    (p : putnam_2011_a1_point) : Prop :=
  exists prefix, points = prefix ++ [p].

Definition putnam_2011_a1_unreachable
    (p : putnam_2011_a1_point) : Prop :=
  0 <= fst p /\ fst p <= 2011 /\
  0 <= snd p /\ snd p <= 2011 /\
  ~ exists spiral,
      putnam_2011_a1_is_spiral spiral /\
      putnam_2011_a1_ends_at spiral p.

Definition putnam_2011_a1_has_cardinality
    {A : Type} (members : A -> Prop) (n : nat) : Prop :=
  exists elements : list A,
    NoDup elements /\
    length elements = n /\
    forall x : A, In x elements <-> members x.

Theorem putnam_2011_a1 :
  putnam_2011_a1_has_cardinality putnam_2011_a1_unreachable 10053.
Admitted.
