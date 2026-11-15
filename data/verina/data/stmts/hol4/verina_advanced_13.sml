(*
  Statement-only formalization of VERINA artifact verina_advanced_13,
  cataloged as "hasChordIntersection": the executable program detects whether
  normalized chords have endpoints that alternate around the circle.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory;

val hasChordIntersection_precond_def = new_definition (
  "hasChordIntersection_precond_def",
  ``hasChordIntersection_precond
      (N : num) (chords : num list list) <=>
      2 <= N /\
      LENGTH chords = N /\
      EVERY
        (\chord : num list.
          LENGTH chord = 2 /\
          1 <= EL 0 chord /\
          EL 0 chord <= 2 * N /\
          1 <= EL 1 chord /\
          EL 1 chord <= 2 * N)
        chords /\
      ALL_DISTINCT (FLAT chords)``
);

val normalizeChord_def = new_definition (
  "normalizeChord_def",
  ``normalizeChord (chord : num list) =
      let a = EL 0 chord in
      let b = EL 1 chord in
        if a > b then [b; a] else [a; b]``
);

val normalizeChords_def = new_definition (
  "normalizeChords_def",
  ``normalizeChords (chords : num list list) =
      MAP normalizeChord chords``
);

val chordInsert_def = Define `
  (chordInsert (x : num list) ([] : num list list) = [x]) /\
  (chordInsert x (y::ys) =
     if EL 0 x < EL 0 y then
       x::y::ys
     else
       y::chordInsert x ys)
`;

val chordSort_def = Define `
  (chordSort ([] : num list list) = ([] : num list list)) /\
  (chordSort (x::xs) =
     chordInsert x (chordSort xs))
`;

val checkChordIntersection_def = Define `
  (checkChordIntersection
      (stack : num list list) ([] : num list list) = F) /\
  (checkChordIntersection stack (chord::rest) =
     let a = EL 0 chord in
     let b = EL 1 chord in
     let newStack =
       dropWhile (\c : num list. EL 1 c < a) stack
     in
       case newStack of
         [] => checkChordIntersection (chord::newStack) rest
       | top::tail =>
           if EL 1 top > a /\ EL 1 top < b then
             T
           else
             checkChordIntersection (chord::newStack) rest)
`;

val hasChordIntersection_def = new_definition (
  "hasChordIntersection_def",
  ``hasChordIntersection (N : num) (chords : num list list) =
      checkChordIntersection
        ([] : num list list)
        (chordSort (normalizeChords chords))``
);

val chordsIntersect_def = new_definition (
  "chordsIntersect_def",
  ``chordsIntersect (chord1 : num list) (chord2 : num list) =
      let a1 = EL 0 chord1 in
      let b1 = EL 1 chord1 in
      let a2 = EL 0 chord2 in
      let b2 = EL 1 chord2 in
        (a1 < a2 /\ a2 < b1 /\ b1 < b2) \/
        (a2 < a1 /\ a1 < b2 /\ b2 < b1)``
);

val checkAllChordPairs_def = Define `
  (checkAllChordPairs ([] : num list list) = F) /\
  (checkAllChordPairs (x::xs) =
     if EXISTS (\y : num list. chordsIntersect x y) xs then
       T
     else
       checkAllChordPairs xs)
`;

val chordsPairwiseNonintersecting_def = Define `
  (chordsPairwiseNonintersecting ([] : num list list) = T) /\
  (chordsPairwiseNonintersecting (x::xs) =
     (EVERY (\y : num list. ~chordsIntersect x y) xs /\
      chordsPairwiseNonintersecting xs))
`;

val hasChordIntersection_postcond_def = new_definition (
  "hasChordIntersection_postcond_def",
  ``hasChordIntersection_postcond
      (N : num)
      (chords : num list list)
      (result : bool) <=>
      let sortedChords = normalizeChords chords
      in
        (chordsPairwiseNonintersecting sortedChords ==> ~result) /\
        (EXISTS
           (\x : num list.
             EXISTS
               (\y : num list. chordsIntersect x y)
               sortedChords)
           sortedChords ==>
         result)``
);

val hasChordIntersection_spec_satisfied =
  ``!(N : num) (chords : num list list).
      hasChordIntersection_precond N chords ==>
      hasChordIntersection_postcond
        N chords (hasChordIntersection N chords)``;
