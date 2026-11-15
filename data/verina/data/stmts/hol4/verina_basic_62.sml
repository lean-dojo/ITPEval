(*
  Statement-only formalization of VERINA corpus artifact verina_basic_62,
  catalog title "Find": the executable linear search returns the first index
  containing the requested integer key, or -1 when the key is absent, under
  its complete correctness contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val Find_precond_def = new_definition (
  "Find_precond_def",
  ``Find_precond (a : int list) (key : int) <=> T``
);

val Find_search_def = Define `
  (Find_search
      (key : int) ([] : int list) (index : num) =
     (~1 : int)) /\
  (Find_search
      key (x::xs) index =
     if x = key then
       int_of_num index
     else
       Find_search key xs (SUC index))
`;

val Find_def = new_definition (
  "Find_def",
  ``Find (a : int list) (key : int) =
      Find_search key a 0``
);

val Find_postcond_def = new_definition (
  "Find_postcond_def",
  ``Find_postcond
      (a : int list) (key : int) (result : int) <=>
      (result = (~1 : int) \/
       (0 <= result /\ result < int_of_num (LENGTH a))) /\
      (result <> (~1 : int) ==>
       (EL (Num result) a = key /\
        (!i : num.
           i < Num result ==>
           EL i a <> key))) /\
      (result = (~1 : int) ==>
       (!i : num.
          i < LENGTH a ==>
          EL i a <> key))``
);

val Find_spec_satisfied =
  ``!(a : int list) (key : int).
      Find_precond a key ==>
      Find_postcond a key (Find a key)``;
