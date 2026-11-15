(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2022_a5:
  the greatest number of squares Alice can guarantee remain uncovered in the
  2022-square adjacent-domino game is 290. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory pred_setTheory;

val putnam_2022_a5 =
  ``let board =
      \x : num set. x SUBSET count 2022
    in
    let valid_move =
      \x : num set.
      \y : num set.
        board x /\
        board y /\
        ((x = y /\
          !i : num. i < 2021 ==> i NOTIN x ==> i + 1 IN x) \/
         ?i : num.
           i < 2021 /\
           i NOTIN x /\
           i + 1 NOTIN x /\
           y = x UNION {i; i + 1})
    in
    let valid_game =
      \g : (num set) list.
        EVERY board g /\
        (?gt : (num set) list. g = {} :: gt) /\
        (!i : num.
           SUC i < LENGTH g
           ==>
           valid_move (EL i g) (EL (SUC i) g))
    in
    let conforms =
      \g : (num set) list.
      \s : num set -> num set.
        EVERY board g /\
        (!x : num set. board x ==> board (s x)) /\
        (!i : num.
           SUC i < LENGTH g /\ EVEN i
           ==>
           EL (SUC i) g = s (EL i g))
    in
    let attainable =
      \n : num.
        ?s : num set -> num set.
          (!x : num set. board x ==> valid_move x (s x)) /\
          (!g : (num set) list.
             valid_game g /\ conforms g s
             ==>
             ?gh : (num set) list. ?x : num set.
               g = gh ++ [x] /\
               n <= CARD (count 2022 DIFF x))
    in
      attainable 290 /\
      !n : num. attainable n ==> n <= 290``;
