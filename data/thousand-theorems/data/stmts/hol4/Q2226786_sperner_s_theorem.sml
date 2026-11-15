(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q2226786, "Sperner's theorem": an antichain in the powerset of a finite type
  has size at most the middle binomial coefficient. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val q2226786_binomial_def = new_definition (
  "q2226786_binomial_def",
  ``q2226786_binomial (n : num) (k : num) =
      CARD {s : num set | s SUBSET count n /\ CARD s = k}``);

val sperner_theorem =
  ``!family : ('a set) set.
      FINITE (UNIV : 'a set) /\
      FINITE family /\
      (!s t. s IN family /\ t IN family /\ s SUBSET t ==> s = t)
      ==>
      CARD family <=
      q2226786_binomial
        (CARD (UNIV : 'a set)) (CARD (UNIV : 'a set) DIV 2)``;
