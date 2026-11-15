(* Statement-only formalization of VERINA corpus artifact verina_advanced_13,
   catalog title "hasChordIntersection": an executable normalization,
   insertion sort, and stack scan for intersecting circle chords, together
   with its correctness contract. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List.

Import ListNotations.

Definition hasChordIntersection_endpoint
    (index : nat) (chord : list nat) : nat :=
  nth index chord 0%nat.

Definition hasChordIntersection_normalizeChord
    (chord : list nat) : list nat :=
  let a := hasChordIntersection_endpoint 0%nat chord in
  let b := hasChordIntersection_endpoint 1%nat chord in
  if Nat.ltb b a then [b; a] else [a; b].

Definition hasChordIntersection_precond
    (N : nat) (chords : list (list nat)) : Prop :=
  (2 <= N)%nat /\
  length chords = N /\
  forallb
    (fun chord =>
      let a := hasChordIntersection_endpoint 0%nat chord in
      let b := hasChordIntersection_endpoint 1%nat chord in
      andb
        (Nat.eqb (length chord) 2%nat)
        (andb
          (Nat.leb 1%nat a)
          (andb
            (Nat.leb a (2 * N)%nat)
            (andb
              (Nat.leb 1%nat b)
              (Nat.leb b (2 * N)%nat)))))
    chords = true /\
  NoDup (concat chords).

Fixpoint hasChordIntersection_dropWhile
    (a : nat) (stack : list (list nat)) : list (list nat) :=
  match stack with
  | [] => []
  | chord :: rest =>
      if Nat.ltb
           (hasChordIntersection_endpoint 1%nat chord)
           a
      then hasChordIntersection_dropWhile a rest
      else stack
  end.

Fixpoint hasChordIntersection_checkIntersection
    (stack remaining : list (list nat)) : bool :=
  match remaining with
  | [] => false
  | chord :: rest =>
      let a := hasChordIntersection_endpoint 0%nat chord in
      let b := hasChordIntersection_endpoint 1%nat chord in
      let newStack := hasChordIntersection_dropWhile a stack in
      match newStack with
      | [] =>
          hasChordIntersection_checkIntersection
            (chord :: newStack) rest
      | top :: _ =>
          let top_b :=
            hasChordIntersection_endpoint 1%nat top in
          if andb (Nat.ltb a top_b) (Nat.ltb top_b b)
          then true
          else
            hasChordIntersection_checkIntersection
              (chord :: newStack) rest
      end
  end.

Fixpoint hasChordIntersection_insert
    (x : list nat) (xs : list (list nat)) : list (list nat) :=
  match xs with
  | [] => [x]
  | y :: ys =>
      if Nat.ltb
           (hasChordIntersection_endpoint 0%nat x)
           (hasChordIntersection_endpoint 0%nat y)
      then x :: xs
      else y :: hasChordIntersection_insert x ys
  end.

Fixpoint hasChordIntersection_sort
    (xs : list (list nat)) : list (list nat) :=
  match xs with
  | [] => []
  | x :: rest =>
      hasChordIntersection_insert
        x (hasChordIntersection_sort rest)
  end.

Definition hasChordIntersection
    (N : nat)
    (chords : list (list nat))
    (_h_precond : hasChordIntersection_precond N chords) : bool :=
  let normalized :=
    map hasChordIntersection_normalizeChord chords in
  let sorted := hasChordIntersection_sort normalized in
  hasChordIntersection_checkIntersection [] sorted.

Definition hasChordIntersection_pair
    (chord1 chord2 : list nat) : bool :=
  let a1 := hasChordIntersection_endpoint 0%nat chord1 in
  let b1 := hasChordIntersection_endpoint 1%nat chord1 in
  let a2 := hasChordIntersection_endpoint 0%nat chord2 in
  let b2 := hasChordIntersection_endpoint 1%nat chord2 in
  orb
    (andb (Nat.ltb a1 a2)
      (andb (Nat.ltb a2 b1) (Nat.ltb b1 b2)))
    (andb (Nat.ltb a2 a1)
      (andb (Nat.ltb a1 b2) (Nat.ltb b2 b1))).

Fixpoint hasChordIntersection_checkAllPairs
    (chords : list (list nat)) : bool :=
  match chords with
  | [] => false
  | x :: xs =>
      if existsb (hasChordIntersection_pair x) xs
      then true
      else hasChordIntersection_checkAllPairs xs
  end.

Definition hasChordIntersection_postcond
    (N : nat)
    (chords : list (list nat))
    (result : bool)
    (_h_precond : hasChordIntersection_precond N chords) : Prop :=
  let normalized :=
    map hasChordIntersection_normalizeChord chords in
  (ForallOrdPairs
     (fun x y =>
       negb (hasChordIntersection_pair x y) = true)
     normalized ->
   ~ result = true) /\
  (existsb
     (fun x =>
       existsb
         (fun y => hasChordIntersection_pair x y)
         normalized)
     normalized = true ->
   result = true).

Theorem hasChordIntersection_spec_satisfied
    (N : nat)
    (chords : list (list nat))
    (h_precond : hasChordIntersection_precond N chords) :
  hasChordIntersection_postcond
    N chords
    (hasChordIntersection N chords h_precond)
    h_precond.
Admitted.
