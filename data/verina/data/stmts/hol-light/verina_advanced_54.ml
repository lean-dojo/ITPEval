(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_54,
  catalog title "missingNumber": an executable natural-number computation
  subtracts the input sum from the triangular sum and returns the unique
  missing value from zero through the list length, under the boundedness and
  duplicate-free precondition. This file contains no proof.
*)

let missingNumber_nodup =
  new_recursive_definition list_RECURSION
    `(missingNumber_nodup ([]:num list) <=> T) /\
     (!x:num. !xs:num list.
        missingNumber_nodup (CONS x xs) <=>
        ~(MEM x xs) /\ missingNumber_nodup xs)`;;

let missingNumber_precond = new_definition
  `missingNumber_precond (nums:num list) <=>
     ALL (\x:num. x <= LENGTH nums) nums /\
     missingNumber_nodup nums`;;

let missingNumber_foldlAdd =
  new_recursive_definition list_RECURSION
    `(!acc:num.
        missingNumber_foldlAdd ([]:num list) acc = acc) /\
     (!x:num. !xs:num list. !acc:num.
        missingNumber_foldlAdd (CONS x xs) acc =
        missingNumber_foldlAdd xs (acc + x))`;;

let missingNumber = new_definition
  `missingNumber (nums:num list) =
     let n = LENGTH nums in
     let expectedSum = (n * (n + 1)) DIV 2 in
     let actualSum = missingNumber_foldlAdd nums 0 in
     expectedSum - actualSum`;;

let missingNumber_range =
  new_recursive_definition num_RECURSION
    `(missingNumber_range 0 = []) /\
     (!n:num.
        missingNumber_range (SUC n) =
        APPEND (missingNumber_range n) (CONS n []))`;;

let missingNumber_postcond = new_definition
  `missingNumber_postcond
      (nums:num list) (result:num) <=>
     let n = LENGTH nums in
     MEM result (missingNumber_range (n + 1)) /\
     ~(MEM result nums) /\
     (!x:num.
        MEM x (missingNumber_range (n + 1))
        ==> ~(x = result)
        ==> MEM x nums)`;;

let missingNumber_spec_satisfied =
  `!nums:num list.
     missingNumber_precond nums
     ==> missingNumber_postcond nums (missingNumber nums)`;;
