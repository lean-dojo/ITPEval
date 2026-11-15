(*
  Statement-only formalization of VERINA artifact verina_advanced_52,
  cataloged as "minOperations": the executable reverse-list scan counts the
  minimum removals from the end needed to collect every natural number from
  1 through k. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory;

val minOperations_targets_def = new_definition (
  "minOperations_targets_def",
  ``minOperations_targets (k : num) =
      MAP (\n : num. n + 1) (COUNT_LIST k)``
);

val minOperations_precond_def = new_definition (
  "minOperations_precond_def",
  ``minOperations_precond (nums : num list) (k : num) <=>
      EVERY (\n : num. MEM n nums) (minOperations_targets k)``
);

val minOperations_loop_def = Define `
  (minOperations_loop
      (k : num)
      ([] : num list)
      (collected : num list)
      (collected_count : num)
      (ops : num) =
     ops) /\
  (minOperations_loop
      k
      (head::tail)
      collected
      collected_count
      ops =
     let ops' = ops + 1
     in
       if 0 < head /\ head <= k /\ ~MEM head collected then
         let collected' = head::collected in
         let collected_count' = collected_count + 1
         in
           if collected_count' = k then
             ops'
           else
             minOperations_loop
               k tail collected' collected_count' ops'
       else
         minOperations_loop
           k tail collected collected_count ops')
`;

val minOperations_def = new_definition (
  "minOperations_def",
  ``minOperations (nums : num list) (k : num) =
      if k = 0 then
        0
      else
        minOperations_loop k (REVERSE nums) [] 0 0``
);

val minOperations_postcond_def = new_definition (
  "minOperations_postcond_def",
  ``minOperations_postcond
      (nums : num list) (k : num) (result : num) <=>
      let processed = TAKE result (REVERSE nums) in
      let target_nums = minOperations_targets k in
      let collected_all =
        EVERY (\n : num. MEM n processed) target_nums in
      let is_minimal =
        if 0 < result then
          ~EVERY
            (\n : num.
              MEM n (TAKE (result - 1) (REVERSE nums)))
            target_nums
        else
          k = 0
      in
        collected_all /\ is_minimal``
);

val minOperations_spec_satisfied =
  ``!(nums : num list) (k : num).
      minOperations_precond nums k ==>
      minOperations_postcond nums k (minOperations nums k)``;
