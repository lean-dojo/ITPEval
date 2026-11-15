(* Statement-only formalization of PutnamBench corpus artifact putnam_2004_a5:
   the expected number of side-connected monochromatic regions in a uniformly
   two-colored finite checkerboard exceeds one eighth of its number of squares.
   This file contains no proof. *)

From Stdlib Require Import Lists.List Arith.PeanoNat Bool.Bool.

Import ListNotations.

Definition putnam_2004_a5_square : Type := (nat * nat)%type.

Definition putnam_2004_a5_coloring : Type :=
  putnam_2004_a5_square -> bool.

Definition putnam_2004_a5_valid_square
    (m n : nat) (p : putnam_2004_a5_square) : Prop :=
  (fst p < m)%nat /\ (snd p < n)%nat.

Definition putnam_2004_a5_adjacent
    (m n : nat)
    (p q : putnam_2004_a5_square) : Prop :=
  putnam_2004_a5_valid_square m n p /\
  putnam_2004_a5_valid_square m n q /\
  ((fst p = fst q /\
    (snd p = S (snd q) \/ snd q = S (snd p))) \/
   (snd p = snd q /\
    (fst p = S (fst q) \/ fst q = S (fst p)))).

Fixpoint putnam_2004_a5_path_adjacency
    (m n : nat)
    (previous : putnam_2004_a5_square)
    (remaining : list putnam_2004_a5_square) : Prop :=
  match remaining with
  | [] => True
  | next :: rest =>
      putnam_2004_a5_adjacent m n previous next /\
      putnam_2004_a5_path_adjacency m n next rest
  end.

Definition putnam_2004_a5_connected
    (m n : nat)
    (C : putnam_2004_a5_coloring)
    (P Q : putnam_2004_a5_square) : Prop :=
  exists tail : list putnam_2004_a5_square,
    last (P :: tail) P = Q /\
    Forall (putnam_2004_a5_valid_square m n) (P :: tail) /\
    (exists color : bool,
      Forall (fun square => C square = color) (P :: tail)) /\
    putnam_2004_a5_path_adjacency m n P tail.

Definition putnam_2004_a5_board_squares
    (m n : nat) : list putnam_2004_a5_square :=
  flat_map
    (fun row =>
      map (fun column => (row, column)) (seq 0 n))
    (seq 0 m).

Definition putnam_2004_a5_same_square
    (p q : putnam_2004_a5_square) : bool :=
  Nat.eqb (fst p) (fst q) && Nat.eqb (snd p) (snd q).

Definition putnam_2004_a5_set_color
    (square : putnam_2004_a5_square)
    (color : bool)
    (C : putnam_2004_a5_coloring) : putnam_2004_a5_coloring :=
  fun candidate =>
    if putnam_2004_a5_same_square candidate square
    then color
    else C candidate.

Fixpoint putnam_2004_a5_all_colorings
    (squares : list putnam_2004_a5_square)
    : list putnam_2004_a5_coloring :=
  match squares with
  | [] => [fun _ => false]
  | square :: remaining =>
      let colorings := putnam_2004_a5_all_colorings remaining in
      map (putnam_2004_a5_set_color square false) colorings ++
      map (putnam_2004_a5_set_color square true) colorings
  end.

Definition putnam_2004_a5_is_region
    (m n : nat)
    (C : putnam_2004_a5_coloring)
    (region : list putnam_2004_a5_square) : Prop :=
  exists representative : putnam_2004_a5_square,
    In representative region /\
    putnam_2004_a5_valid_square m n representative /\
    forall square : putnam_2004_a5_square,
      In square region <->
      putnam_2004_a5_valid_square m n square /\
      putnam_2004_a5_connected m n C representative square.

Definition putnam_2004_a5_region_decomposition
    (m n : nat)
    (C : putnam_2004_a5_coloring)
    (regions : list (list putnam_2004_a5_square)) : Prop :=
  NoDup regions /\
  Forall (fun region => NoDup region) regions /\
  (forall region : list putnam_2004_a5_square,
    In region regions ->
    putnam_2004_a5_is_region m n C region) /\
  (forall square : putnam_2004_a5_square,
    putnam_2004_a5_valid_square m n square ->
    exists! region : list putnam_2004_a5_square,
      In region regions /\ In square region).

Definition putnam_2004_a5_counts_regions
    (m n : nat)
    (cmr : putnam_2004_a5_coloring -> nat) : Prop :=
  forall C : putnam_2004_a5_coloring,
    exists regions : list (list putnam_2004_a5_square),
      putnam_2004_a5_region_decomposition m n C regions /\
      cmr C = length regions.

Definition putnam_2004_a5_total_regions
    (m n : nat)
    (cmr : putnam_2004_a5_coloring -> nat) : nat :=
  fold_right Nat.add 0%nat
    (map cmr
      (putnam_2004_a5_all_colorings
        (putnam_2004_a5_board_squares m n))).

Theorem putnam_2004_a5
    (m n : nat)
    (mnpos : (0 < m * n)%nat)
    (cmr : putnam_2004_a5_coloring -> nat)
    (hcmr : putnam_2004_a5_counts_regions m n cmr) :
  (Nat.pow 2 (m * n) * (m * n) <
   8 * putnam_2004_a5_total_regions m n cmr)%nat.
Admitted.
