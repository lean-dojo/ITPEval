(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q2253746, "Bertrand's ballot theorem": when candidate A receives p votes
  and candidate B receives q votes with q < p, the uniform proportion of
  countings whose every nonempty suffix has positive A-minus-B sum is
  (p - q) / (p + q). This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory pred_setTheory;

val q2253746_int_sum_def = Define`
  (q2253746_int_sum ([] : int list) = 0) /\
  (q2253746_int_sum (x::xs) = x + q2253746_int_sum xs)
`;

val q2253746_stays_positive_def = Define`
  (q2253746_stays_positive ([] : int list) = T) /\
  (q2253746_stays_positive (x::xs) =
     (0 < q2253746_int_sum (x::xs) /\
      q2253746_stays_positive xs))
`;

val q2253746_counted_sequence_def = new_definition (
  "q2253746_counted_sequence_def",
  ``q2253746_counted_sequence (p : num) (q : num) (votes : int list) <=>
      LENGTH (FILTER (\x : int. x = 1) votes) = p /\
      LENGTH (FILTER (\x : int. x = -1) votes) = q /\
      EVERY (\x : int. x = 1 \/ x = -1) votes``);

val q2253746_counted_sequences_def = new_definition (
  "q2253746_counted_sequences_def",
  ``q2253746_counted_sequences (p : num) (q : num) =
      {votes : int list | q2253746_counted_sequence p q votes}``);

val q2253746_positive_sequences_def = new_definition (
  "q2253746_positive_sequences_def",
  ``q2253746_positive_sequences (p : num) (q : num) =
      {votes : int list |
         q2253746_counted_sequence p q votes /\
         q2253746_stays_positive votes}``);

val ballot_problem =
  ``!q p : num.
      q < p
      ==>
      CARD (q2253746_positive_sequences p q) * (p + q) =
        (p - q) * CARD (q2253746_counted_sequences p q)``;
