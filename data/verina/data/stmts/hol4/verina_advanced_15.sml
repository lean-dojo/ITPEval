(*
  Statement-only formalization of VERINA artifact verina_advanced_15,
  cataloged as "increasingTriplet": the executable Boolean program detects
  whether an integer list contains a strictly increasing subsequence of
  length three. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory optionTheory;

val increasingTriplet_precond_def = new_definition (
  "increasingTriplet_precond_def",
  ``increasingTriplet_precond (nums : int list) <=> T``
);

val increasingTriplet_loop_def = Define `
  (increasingTriplet_loop
      ([] : int list) (first : int option) (second : int option) = F) /\
  (increasingTriplet_loop (x::xs) NONE second =
     increasingTriplet_loop xs (SOME x) NONE) /\
  (increasingTriplet_loop (x::xs) (SOME f) NONE =
     if x <= f then
       increasingTriplet_loop xs (SOME x) NONE
     else
       increasingTriplet_loop xs (SOME f) (SOME x)) /\
  (increasingTriplet_loop (x::xs) (SOME f) (SOME s) =
     if x <= f then
       increasingTriplet_loop xs (SOME x) (SOME s)
     else if x <= s then
       increasingTriplet_loop xs (SOME f) (SOME x)
     else
       T)
`;

val increasingTriplet_def = new_definition (
  "increasingTriplet_def",
  ``increasingTriplet (nums : int list) =
      if LENGTH nums < 3 then
        F
      else
        increasingTriplet_loop nums NONE NONE``
);

val increasingTriplet_zipIdxFrom_def = Define `
  (increasingTriplet_zipIdxFrom
      (index : num) ([] : int list) = ([] : (int # num) list)) /\
  (increasingTriplet_zipIdxFrom index (x::xs) =
     (x,index)::increasingTriplet_zipIdxFrom (SUC index) xs)
`;

val increasingTriplet_zipIdx_def = new_definition (
  "increasingTriplet_zipIdx_def",
  ``increasingTriplet_zipIdx (nums : int list) =
      increasingTriplet_zipIdxFrom 0 nums``
);

val increasingTriplet_postcond_def = new_definition (
  "increasingTriplet_postcond_def",
  ``increasingTriplet_postcond
      (nums : int list) (result : bool) <=>
      let nums' = increasingTriplet_zipIdx nums
      in
        (result ==>
          EXISTS
            (\xi : int # num.
              EXISTS
                (\yj : int # num.
                  EXISTS
                    (\zk : int # num.
                      SND xi < SND yj /\
                      SND yj < SND zk /\
                      FST xi < FST yj /\
                      FST yj < FST zk)
                    nums')
                nums')
            nums') /\
        (~result ==>
          EVERY
            (\xi : int # num.
              EVERY
                (\yj : int # num.
                  EVERY
                    (\zk : int # num.
                      SND xi >= SND yj \/
                      SND yj >= SND zk \/
                      FST xi >= FST yj \/
                      FST yj >= FST zk)
                    nums')
                nums')
            nums')``
);

val increasingTriplet_spec_satisfied =
  ``!nums : int list.
      increasingTriplet_precond nums ==>
      increasingTriplet_postcond nums (increasingTriplet nums)``;
