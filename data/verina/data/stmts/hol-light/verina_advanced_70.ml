(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_70,
  catalog title "semiOrderedPermutation": a deterministic index-based program
  computes the minimum adjacent swaps needed to place 1 first and n last in a
  permutation of the integers from 1 through n. This file contains no proof.
*)

let semiOrderedPermutation_nodup =
  new_recursive_definition list_RECURSION
    `(semiOrderedPermutation_nodup ([]:int list) <=> T) /\
     (!x:int. !xs:int list.
        semiOrderedPermutation_nodup (CONS x xs) <=>
        ~(MEM x xs) /\ semiOrderedPermutation_nodup xs)`;;

let semiOrderedPermutation_precond = new_definition
  `semiOrderedPermutation_precond (nums:int list) <=>
     let n = LENGTH nums in
     0 < n /\
     semiOrderedPermutation_nodup nums /\
     ALL (\x:int. (&1:int) <= x /\ x <= &n) nums`;;

let semiOrderedPermutation_idxOf =
  new_recursive_definition list_RECURSION
    `(semiOrderedPermutation_idxOf (value:int) [] = 0) /\
     (!x:int. !xs:int list. !value:int.
        semiOrderedPermutation_idxOf value (CONS x xs) =
        if x = value then 0
        else SUC (semiOrderedPermutation_idxOf value xs))`;;

let semiOrderedPermutation = new_definition
  `semiOrderedPermutation (nums:int list) =
     let lengthList = LENGTH nums in
     let numOne = (&1:int) in
     let largestNum = (&lengthList:int) in
     let firstIndex = semiOrderedPermutation_idxOf numOne nums in
     let lastIndex = semiOrderedPermutation_idxOf largestNum nums in
     let startPosition = 0 in
     let endPosition = lengthList - 1 in
     let shouldMoveOne = ~(firstIndex = startPosition) in
     let shouldMoveLast = ~(lastIndex = endPosition) in
     let distanceOne = if shouldMoveOne then firstIndex else 0 in
     let distanceLast =
       if shouldMoveLast then endPosition - lastIndex else 0 in
     let totalMoves = distanceOne + distanceLast in
     let needAdjustment = firstIndex > lastIndex in
     let adjustedMoves =
       if needAdjustment then totalMoves - 1 else totalMoves in
     (&adjustedMoves:int)`;;

let semiOrderedPermutation_postcond = new_definition
  `semiOrderedPermutation_postcond
      (nums:int list) (result:int) <=>
     let n = LENGTH nums in
     let pos1 = semiOrderedPermutation_idxOf (&1:int) nums in
     let posn = semiOrderedPermutation_idxOf (&n:int) nums in
     if pos1 > posn then
       (&pos1:int) + &n = result + &2 + &posn
     else
       (&pos1:int) + &n = result + &1 + &posn`;;

let semiOrderedPermutation_spec_satisfied =
  `!nums:int list.
     semiOrderedPermutation_precond nums
     ==> semiOrderedPermutation_postcond
           nums (semiOrderedPermutation nums)`;;
