(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_60,
  catalog title "partitionEvensOdds": an executable recursive stable partition
  separates a list of natural numbers into its even and odd elements, together
  with its total correctness contract. This file contains no proof.
*)

let partitionEvensOdds_precond = new_definition
  `partitionEvensOdds_precond (nums:num list) <=> T`;;

let partitionEvensOdds_helper =
  new_recursive_definition list_RECURSION
    `(partitionEvensOdds_helper ([]:num list) =
        (([]:num list),([]:num list))) /\
     (!x:num. !xs:num list.
        partitionEvensOdds_helper (CONS x xs) =
        let result = partitionEvensOdds_helper xs in
        if x MOD 2 = 0 then
          (CONS x (FST result),SND result)
        else
          (FST result,CONS x (SND result)))`;;

let partitionEvensOdds = new_definition
  `partitionEvensOdds (nums:num list) =
     partitionEvensOdds_helper nums`;;

let partitionEvensOdds_postcond = new_definition
  `partitionEvensOdds_postcond
      (nums:num list) (result:num list#num list) <=>
     let evens = FST result in
     let odds = SND result in
     APPEND evens odds =
       APPEND
         (FILTER (\n:num. n MOD 2 = 0) nums)
         (FILTER (\n:num. n MOD 2 = 1) nums) /\
     ALL (\n:num. n MOD 2 = 0) evens /\
     ALL (\n:num. n MOD 2 = 1) odds`;;

let partitionEvensOdds_spec_satisfied =
  `!nums:num list.
     partitionEvensOdds_precond nums
     ==> partitionEvensOdds_postcond
           nums (partitionEvensOdds nums)`;;
