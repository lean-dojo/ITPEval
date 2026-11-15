(*
  Statement-only formalization of VERINA artifact verina_advanced_43,
  cataloged as "maxStrength": the executable subset-enumeration program
  returns the maximum product of a nonempty subset of a nonempty integer
  list. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory optionTheory;

val maxStrength_precond_def = new_definition (
  "maxStrength_precond_def",
  ``maxStrength_precond (nums : int list) <=>
      ~(nums = [])``
);

val maxStrength_interleave_def = Define `
  (maxStrength_interleave
      (x : int) ([] : int list list) =
     ([] : int list list)) /\
  (maxStrength_interleave x (subset::subsets) =
     subset :: (x::subset) :: maxStrength_interleave x subsets)
`;

val maxStrength_powerSet_def = Define `
  (maxStrength_powerSet ([] : int list) =
     ([[]] : int list list)) /\
  (maxStrength_powerSet (x::xs) =
     maxStrength_interleave x (maxStrength_powerSet xs))
`;

val maxStrength_product_def = new_definition (
  "maxStrength_product_def",
  ``maxStrength_product (subset : int list) =
      FOLDL (\acc x. acc * x) (1 : int) subset``
);

val maxStrength_maxOpt_def = Define `
  (maxStrength_maxOpt ([] : int list) =
     (NONE : int option)) /\
  (maxStrength_maxOpt (x::xs) =
     case maxStrength_maxOpt xs of
       NONE => SOME x
     | SOME best => SOME (if x < best then best else x))
`;

val maxStrength_def = new_definition (
  "maxStrength_def",
  ``maxStrength (nums : int list) =
      let subsets = maxStrength_powerSet nums in
      let nonEmpty =
        FILTER (\subset : int list. ~(subset = [])) subsets
      in
      let products = MAP maxStrength_product nonEmpty
      in
        case maxStrength_maxOpt products of
          NONE => (-1000000 : int)
        | SOME result => result``
);

val maxStrength_sublists_def = Define `
  (maxStrength_sublists ([] : int list) =
     ([[]] : int list list)) /\
  (maxStrength_sublists (x::xs) =
     let rest = maxStrength_sublists xs
     in
       rest ++ MAP (\subset. x::subset) rest)
`;

val maxStrength_postcond_def = new_definition (
  "maxStrength_postcond_def",
  ``maxStrength_postcond
      (nums : int list) (result : int) <=>
      let sublists =
        FILTER
          (\subset : int list. ~(subset = []))
          (maxStrength_sublists nums)
      in
      let products = MAP maxStrength_product sublists
      in
        MEM result products /\
        EVERY (\product : int. product <= result) products``
);

val maxStrength_spec_satisfied =
  ``!nums : int list.
      maxStrength_precond nums ==>
      maxStrength_postcond nums (maxStrength nums)``;
