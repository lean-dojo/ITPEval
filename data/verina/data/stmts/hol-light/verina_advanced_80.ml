(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_80,
  catalog title "twoSum": a fuel-bounded nested scan of an integer array
  returns the unique increasing pair of indices whose values sum to the
  target, together with its precondition and correctness contract.
  This file contains no proof.
*)

let twoSum_range =
  new_recursive_definition num_RECURSION
    `(twoSum_range 0 = []) /\
     (!n:num.
        twoSum_range (SUC n) =
        APPEND (twoSum_range n) (CONS n []))`;;

let twoSum_pairsFor = new_definition
  `twoSum_pairsFor
      (nums:int list) (target:int) (i:num) =
     MAP (\j:num. (i,j))
       (FILTER
         (\j:num. EL i nums + EL j nums = target)
         (twoSum_range i))`;;

let twoSum_flatMapPairs =
  new_recursive_definition list_RECURSION
    `(!nums:int list. !target:int.
        twoSum_flatMapPairs ([]:num list) nums target = []) /\
     (!i:num. !is:num list. !nums:int list. !target:int.
        twoSum_flatMapPairs (CONS i is) nums target =
        APPEND
          (twoSum_pairsFor nums target i)
          (twoSum_flatMapPairs is nums target))`;;

let twoSum_matchingPairs = new_definition
  `twoSum_matchingPairs (nums:int list) (target:int) =
     twoSum_flatMapPairs
       (twoSum_range (LENGTH nums)) nums target`;;

let twoSum_precond = new_definition
  `twoSum_precond (nums:int list) (target:int) <=>
     2 <= LENGTH nums /\
     ~(twoSum_matchingPairs nums target = []) /\
     LENGTH (twoSum_matchingPairs nums target) = 1`;;

let twoSum_findIndices =
  new_recursive_definition num_RECURSION
    `(!nums:int list. !target:int. !i:num. !j:num.
        twoSum_findIndices 0 nums target i j = []) /\
     (!fuel:num. !nums:int list. !target:int. !i:num. !j:num.
        twoSum_findIndices (SUC fuel) nums target i j =
        if LENGTH nums <= i then
          []
        else if LENGTH nums <= j then
          twoSum_findIndices fuel nums target (i + 1) (i + 2)
        else if EL i nums + EL j nums = target then
          CONS i (CONS j [])
        else
          twoSum_findIndices fuel nums target i (j + 1))`;;

let twoSum = new_definition
  `twoSum (nums:int list) (target:int) =
     twoSum_findIndices
       (LENGTH nums * LENGTH nums) nums target 0 1`;;

let twoSum_postcond = new_definition
  `twoSum_postcond
      (nums:int list) (target:int) (result:num list) <=>
     LENGTH result = 2 /\
     EL 0 result < LENGTH nums /\
     EL 1 result < LENGTH nums /\
     EL 0 result < EL 1 result /\
     EL (EL 0 result) nums + EL (EL 1 result) nums = target`;;

let twoSum_spec_satisfied =
  `!nums:int list. !target:int.
     twoSum_precond nums target
     ==> twoSum_postcond nums target (twoSum nums target)`;;
