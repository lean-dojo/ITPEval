(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  thousand-theorems__hol4__Q422187, "Myhill–Nerode theorem": a language of
  words over an arbitrary type is recognized by a finite-state deterministic
  automaton if and only if its set of left quotients is finite. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory pred_setTheory;

val q422187_run_def = Define`
  (q422187_run step q [] = q) /\
  (q422187_run step q (a::w) = q422187_run step (step q a) w)
`;

val q422187_left_quotient_def = new_definition (
  "q422187_left_quotient_def",
  ``q422187_left_quotient (L : 'a list set) x =
      {y | APPEND x y IN L}``
);

val q422187_is_regular_def = new_definition (
  "q422187_is_regular_def",
  ``q422187_is_regular (L : 'a list set) <=>
      ?n start (step : num -> 'a -> num) (accept : num set).
        0 < n /\
        start < n /\
        (!q a. q < n ==> step q a < n) /\
        (!q. q IN accept ==> q < n) /\
        (!w. w IN L <=> q422187_run step start w IN accept)``
);

val q422187_myhill_nerode_theorem =
  ``!(L : 'a list set).
      q422187_is_regular L <=>
      FINITE (IMAGE (q422187_left_quotient L) UNIV)``;
