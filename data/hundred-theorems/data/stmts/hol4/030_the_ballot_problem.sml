(*
  Statement-only formalization of "The Ballot Problem" from Hundred Theorems item 030. This file
  contains no proof.
*)

(*
  Hundred Theorems item 030, "The Ballot Problem": among vote sequences with a votes for A
  and b votes for B, the number in which A is strictly ahead after every nonempty prefix
  satisfies the classical ballot counting identity. This is a statement-only formalization
  and contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory pred_setTheory;

val ballot_problem =
  ``let count_a =
      \votes : bool list. LENGTH (FILTER (\vote. vote) votes)
    in
    let count_b =
      \votes : bool list. LENGTH (FILTER (\vote. ~vote) votes)
    in
    let all_countings =
      \a b : num.
        CARD
          {votes : bool list |
             LENGTH votes = a + b /\
             count_a votes = a /\
             count_b votes = b}
    in
    let valid_countings =
      \a b : num.
        CARD
          {votes : bool list |
             LENGTH votes = a + b /\
             count_a votes = a /\
             count_b votes = b /\
             !m.
               0 < m /\ m <= LENGTH votes ==>
               count_b (TAKE m votes) < count_a (TAKE m votes)}
    in
      !a b : num.
        (a + b) * valid_countings a b =
        (a - b) * all_countings a b``;
