(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2012_b3:
  in every round-robin tournament on 2n teams, one can choose a winning team
  from each of the 2n - 1 days without choosing any team twice. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val putnam_2012_b3 =
  ``let matchup_games =
      \n (matchups : num -> num -> num).
        !d t : num.
          d < 2 * n - 1 /\ t < 2 * n
          ==>
          matchups d t < 2 * n /\
          matchups d t <> t /\
          matchups d (matchups d t) = t
    in
    let matchup_all =
      \n (matchups : num -> num -> num).
        !t1 t2 : num.
          t1 < 2 * n /\ t2 < 2 * n /\ t1 <> t2
          ==>
          ?d : num. d < 2 * n - 1 /\ matchups d t1 = t2
    in
    let matchup_wins =
      \n (matchups : num -> num -> num) (wins : num -> num -> bool).
        !d t : num.
          d < 2 * n - 1 /\ t < 2 * n
          ==>
          (wins d t <=> ~wins d (matchups d t))
    in
    let winning_choices =
      \n (wins : num -> num -> bool).
        ?choices : num -> num.
          (!d : num.
             d < 2 * n - 1
             ==>
             choices d < 2 * n /\ wins d (choices d)) /\
          INJ choices (count (2 * n - 1)) (count (2 * n))
    in
      ((!n : num.
          1 <= n
          ==>
          !matchups : num -> num -> num.
          !wins : num -> num -> bool.
            matchup_games n matchups /\
            matchup_all n matchups /\
            matchup_wins n matchups wins
            ==>
            winning_choices n wins)
       <=>
       T)``;
