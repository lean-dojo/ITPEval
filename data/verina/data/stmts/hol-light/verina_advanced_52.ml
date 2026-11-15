(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_52,
  catalog title "minOperations": an executable reverse-list scan computes the
  minimum number of removals from the end needed to collect every natural
  number from 1 through k, with its occurrence precondition and minimal-prefix
  postcondition. This file contains no proof.
*)

let minOperations_range =
  new_recursive_definition num_RECURSION
    `(minOperations_range 0 = []) /\
     (!n:num.
        minOperations_range (SUC n) =
        APPEND (minOperations_range n) (CONS n []))`;;

let minOperations_targetNums = new_definition
  `minOperations_targetNums (k:num) =
     MAP (\n:num. n + 1) (minOperations_range k)`;;

let minOperations_precond = new_definition
  `minOperations_precond (nums:num list) (k:num) <=>
     ALL
       (\n:num. MEM n nums)
       (minOperations_targetNums k)`;;

let minOperations_loop =
  new_recursive_definition list_RECURSION
    `(!k:num. !collected:num list. !collected_count:num. !ops:num.
        minOperations_loop
          ([]:num list) k collected collected_count ops =
        ops) /\
     (!head:num. !tail:num list. !k:num. !collected:num list.
      !collected_count:num. !ops:num.
        minOperations_loop
          (CONS head tail) k collected collected_count ops =
        let ops' = ops + 1 in
        if
          head > 0 /\
          head <= k /\
          ~(MEM head collected)
        then
          let collected' = CONS head collected in
          let collected_count' = collected_count + 1 in
          if collected_count' = k then
            ops'
          else
            minOperations_loop
              tail k collected' collected_count' ops'
        else
          minOperations_loop
            tail k collected collected_count ops')`;;

let minOperations = new_definition
  `minOperations (nums:num list) (k:num) =
     if k = 0 then 0
     else
       minOperations_loop
         (REVERSE nums) k [] 0 0`;;

let minOperations_take =
  new_recursive_definition num_RECURSION
    `(!xs:num list.
        minOperations_take 0 xs = []) /\
     (!n:num. !xs:num list.
        minOperations_take (SUC n) xs =
        if xs = [] then []
        else
          CONS (HD xs)
            (minOperations_take n (TL xs)))`;;

let minOperations_postcond = new_definition
  `minOperations_postcond
      (nums:num list) (k:num) (result:num) <=>
     let processed =
       minOperations_take result (REVERSE nums) in
     let target_nums =
       minOperations_targetNums k in
     let collected_all =
       ALL (\n:num. MEM n processed) target_nums in
     let is_minimal =
       if result > 0 then
         let processed_minus_one =
           minOperations_take
             (result - 1) (REVERSE nums) in
         ~(ALL
            (\n:num. MEM n processed_minus_one)
            target_nums)
       else
         k = 0 in
     collected_all /\ is_minimal`;;

let minOperations_spec_satisfied =
  `!nums:num list. !k:num.
     minOperations_precond nums k
     ==> minOperations_postcond
           nums k (minOperations nums k)`;;
