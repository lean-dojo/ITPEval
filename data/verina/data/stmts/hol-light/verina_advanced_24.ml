(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_24,
  catalog title "lengthOfLIS": an executable patience-sorting list fold computes
  the length of a longest strictly increasing integer subsequence, with its
  total precondition and exhaustive-subsequence maximality postcondition. This
  file contains no proof.
*)

let lengthOfLIS_precond = new_definition
  `lengthOfLIS_precond (nums:int list) <=> T`;;

let lengthOfLIS_replace =
  new_recursive_definition list_RECURSION
    `(!x:int. !acc:int list.
        lengthOfLIS_replace x acc [] =
        APPEND (REVERSE acc) (CONS x [])) /\
     (!y:int. !ys:int list. !x:int. !acc:int list.
        lengthOfLIS_replace x acc (CONS y ys) =
        if x <= y then
          APPEND (REVERSE acc) (CONS x ys)
        else
          lengthOfLIS_replace x (CONS y acc) ys)`;;

let lengthOfLIS_lisHelper = new_definition
  `lengthOfLIS_lisHelper (dp:int list) (x:int) =
     lengthOfLIS_replace x [] dp`;;

let lengthOfLIS_fold =
  new_recursive_definition list_RECURSION
    `(!dp:int list.
        lengthOfLIS_fold [] dp = dp) /\
     (!x:int. !xs:int list. !dp:int list.
        lengthOfLIS_fold (CONS x xs) dp =
        lengthOfLIS_fold xs (lengthOfLIS_lisHelper dp x))`;;

let lengthOfLIS = new_definition
  `lengthOfLIS (nums:int list) =
     (&(LENGTH (lengthOfLIS_fold nums [])):int)`;;

let lengthOfLIS_isStrictlyIncreasing =
  new_recursive_definition list_RECURSION
    `(lengthOfLIS_isStrictlyIncreasing ([]:int list) <=> T) /\
     (!x:int. !xs:int list.
        lengthOfLIS_isStrictlyIncreasing (CONS x xs) <=>
        if xs = [] then T
        else x < HD xs /\ lengthOfLIS_isStrictlyIncreasing xs)`;;

let lengthOfLIS_subsequences =
  new_recursive_definition list_RECURSION
    `(lengthOfLIS_subsequences ([]:int list) =
        CONS ([]:int list) []) /\
     (!x:int. !xs:int list.
        lengthOfLIS_subsequences (CONS x xs) =
        let rest = lengthOfLIS_subsequences xs in
        APPEND rest (MAP (\r:int list. CONS x r) rest))`;;

let lengthOfLIS_postcond = new_definition
  `lengthOfLIS_postcond (nums:int list) (result:int) <=>
     let allIncreasing =
       FILTER lengthOfLIS_isStrictlyIncreasing
         (lengthOfLIS_subsequences nums) in
     EX (\l:int list. &(LENGTH l) = result) allIncreasing /\
     ALL (\l:int list. &(LENGTH l) <= result) allIncreasing`;;

let lengthOfLIS_spec_satisfied =
  `!nums:int list.
     lengthOfLIS_precond nums
     ==> lengthOfLIS_postcond nums (lengthOfLIS nums)`;;
