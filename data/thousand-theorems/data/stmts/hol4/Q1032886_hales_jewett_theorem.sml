(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1032886, "Hales–Jewett theorem": for every finite alphabet and finite color
  type, some finite-dimensional word space has a monochromatic combinatorial
  line with at least one variable coordinate. This file contains no proof.
*)

open HolKernel Parse boolLib;
open listTheory pred_setTheory;

val q1032886_word_def = new_definition (
  "q1032886_word_def",
  ``q1032886_word (A : 'a set) (n : num) (w : 'a list) <=>
      LENGTH w = n /\
      EVERY (\a. a IN A) w``);

val q1032886_line_def = new_definition (
  "q1032886_line_def",
  ``q1032886_line
      (A : 'a set) (n : num) (line : 'a option list) <=>
      LENGTH line = n /\
      MEM NONE line /\
      EVERY
        (\entry.
           case entry of NONE => T | SOME a => a IN A)
        line``);

val q1032886_line_eval_def = new_definition (
  "q1032886_line_eval_def",
  ``q1032886_line_eval (line : 'a option list) (x : 'a) =
      MAP
        (\entry. case entry of NONE => x | SOME a => a)
        line``);

val hales_jewett_theorem =
  ``!A : 'a set. !K : 'k set.
      FINITE A /\ FINITE K
      ==>
      ?n.
        !C : 'a list -> 'k.
          (!w.
             q1032886_word A n w ==>
             C w IN K)
          ==>
          ?line : 'a option list. ?c : 'k.
            q1032886_line A n line /\
            c IN K /\
            !x.
              x IN A
              ==>
              C (q1032886_line_eval line x) = c``;
