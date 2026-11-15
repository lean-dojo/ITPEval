(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_63,
  catalog title "removeDuplicates": a deterministic recursive scan counts the
  distinct entries of a nondecreasing integer list and is connected to the
  duplicate-erasure length contract. This file contains no proof.
*)

let removeDuplicates_precond = new_definition
  `removeDuplicates_precond (nums:int list) <=>
     PAIRWISE (\x y:int. x <= y) nums`;;

let removeDuplicates_countUniques =
  new_recursive_definition list_RECURSION
    `(!prev:int. !k:num.
        removeDuplicates_countUniques prev ([]:int list) k = k) /\
     (!head:int. !tail:int list. !prev:int. !k:num.
        removeDuplicates_countUniques prev (CONS head tail) k =
        if head = prev then
          removeDuplicates_countUniques prev tail k
        else
          removeDuplicates_countUniques head tail (k + 1))`;;

let removeDuplicates = new_definition
  `removeDuplicates (nums:int list) =
     if nums = [] then 0
     else
       removeDuplicates_countUniques
         (HD nums) (TL nums) 1`;;

let removeDuplicates_eraseDupsLoop =
  new_recursive_definition list_RECURSION
    `(!seenReversed:int list.
        removeDuplicates_eraseDupsLoop
          ([]:int list) seenReversed =
        REVERSE seenReversed) /\
     (!x:int. !xs:int list. !seenReversed:int list.
        removeDuplicates_eraseDupsLoop
          (CONS x xs) seenReversed =
        if MEM x seenReversed then
          removeDuplicates_eraseDupsLoop xs seenReversed
        else
          removeDuplicates_eraseDupsLoop
            xs (CONS x seenReversed))`;;

let removeDuplicates_eraseDups = new_definition
  `removeDuplicates_eraseDups (nums:int list) =
     removeDuplicates_eraseDupsLoop nums []`;;

let removeDuplicates_postcond = new_definition
  `removeDuplicates_postcond
      (nums:int list) (result:num) <=>
     result - LENGTH (removeDuplicates_eraseDups nums) = 0 /\
     LENGTH (removeDuplicates_eraseDups nums) <= result`;;

let removeDuplicates_spec_satisfied =
  `!nums:int list.
     removeDuplicates_precond nums
     ==> removeDuplicates_postcond
           nums (removeDuplicates nums)`;;
