(*
  Statement-only formalization of VERINA artifact verina_advanced_8,
  cataloged as "canCompleteCircuit": the executable greedy scan selects the
  least gas-station index from which every circular prefix has nonnegative
  fuel, or returns -1 when no such index exists. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory pairTheory;

val canCompleteCircuit_precond_def = new_definition (
  "canCompleteCircuit_precond_def",
  ``canCompleteCircuit_precond
      (gas : int list) (cost : int list) <=>
      0 < LENGTH gas /\ LENGTH gas = LENGTH cost``
);

val canCompleteCircuit_loop_def = Define `
  (canCompleteCircuit_loop
      ([] : int list)
      ([] : int list)
      (idx : num)
      (tank : int)
      (start : num) =
     int_of_num start) /\
  (canCompleteCircuit_loop
      (gi::gs)
      (ci::cs)
      idx
      tank
      start =
     let tank' = tank + gi - ci in
     if tank' < 0 then
       canCompleteCircuit_loop gs cs (idx + 1) 0 (idx + 1)
     else
       canCompleteCircuit_loop gs cs (idx + 1) tank' start) /\
  (canCompleteCircuit_loop
      ([] : int list)
      (ci::cs)
      idx
      tank
      start =
     (~1 : int)) /\
  (canCompleteCircuit_loop
      (gi::gs)
      ([] : int list)
      idx
      tank
      start =
     (~1 : int))
`;

val canCompleteCircuit_zip_def = Define `
  (canCompleteCircuit_zip
      ([] : int list)
      (ys : int list) =
     ([] : (int # int) list)) /\
  (canCompleteCircuit_zip
      (x::xs)
      ([] : int list) =
     ([] : (int # int) list)) /\
  (canCompleteCircuit_zip
      (x::xs)
      (y::ys) =
     (x,y)::canCompleteCircuit_zip xs ys)
`;

val canCompleteCircuit_walk_def = Define `
  (canCompleteCircuit_walk
      ([] : (int # int) list)
      (i : num)
      (tank : int)
      (start : num) =
     int_of_num start) /\
  (canCompleteCircuit_walk
      ((g,c)::rest)
      i
      tank
      start =
     let newTank = tank + g - c in
     if newTank < 0 then
       canCompleteCircuit_walk rest (i + 1) 0 (i + 1)
     else
       canCompleteCircuit_walk rest (i + 1) newTank start)
`;

val canCompleteCircuit_def = new_definition (
  "canCompleteCircuit_def",
  ``canCompleteCircuit
      (gas : int list) (cost : int list) =
      let totalGas =
        FOLDL (\acc : int. \g : int. acc + g) 0 gas in
      let totalCost =
        FOLDL (\acc : int. \c : int. acc + c) 0 cost in
      if totalGas < totalCost then
        (~1 : int)
      else
        let zipped = canCompleteCircuit_zip gas cost
        in
          canCompleteCircuit_walk zipped 0 0 0``
);

val canCompleteCircuit_valid_def = new_definition (
  "canCompleteCircuit_valid_def",
  ``canCompleteCircuit_valid
      (gas : int list) (cost : int list) (start : num) <=>
      EVERY
        (\i : num.
           0 <=
             FOLDL
               (\tank : int.
                  \j : num.
                    let jdx = (start + j) MOD LENGTH gas
                    in
                      tank + EL jdx gas - EL jdx cost)
               0
               (COUNT_LIST (i + 1)))
        (COUNT_LIST (LENGTH gas))``
);

val canCompleteCircuit_postcond_def = new_definition (
  "canCompleteCircuit_postcond_def",
  ``canCompleteCircuit_postcond
      (gas : int list) (cost : int list) (result : int) <=>
      (~1 : int) <= result /\
      (result = (~1 : int) ==>
        EVERY
          (\start : num.
             ~canCompleteCircuit_valid gas cost start)
          (COUNT_LIST (LENGTH gas))) /\
      (0 <= result ==>
        result < int_of_num (LENGTH gas) /\
        canCompleteCircuit_valid gas cost (Num result) /\
        EVERY
          (\start : num.
             ~canCompleteCircuit_valid gas cost start)
          (COUNT_LIST (Num result)))``
);

val canCompleteCircuit_spec_satisfied =
  ``!(gas : int list) (cost : int list).
      canCompleteCircuit_precond gas cost ==>
      canCompleteCircuit_postcond
        gas cost (canCompleteCircuit gas cost)``;
