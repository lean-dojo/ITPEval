(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_57,
  catalog title "nextGreaterElement": an executable monotone-stack scan maps
  each distinct integer in a list to the first greater integer to its right,
  then looks up those answers for a distinct query list drawn from it, together
  with the full correctness contract. This file contains no proof.
*)

let nextGreaterElement_nodup =
  new_recursive_definition list_RECURSION
    `(nextGreaterElement_nodup ([]:int list) <=> T) /\
     (!x:int. !xs:int list.
        nextGreaterElement_nodup (CONS x xs) <=>
        ~MEM x xs /\ nextGreaterElement_nodup xs)`;;

let nextGreaterElement_precond = new_definition
  `nextGreaterElement_precond
      (nums1:int list) (nums2:int list) <=>
     nextGreaterElement_nodup nums1 /\
     nextGreaterElement_nodup nums2 /\
     ALL (\x:int. MEM x nums2) nums1`;;

let nextGreaterElement_getAt =
  new_recursive_definition num_RECURSION
    `(!xs:int list.
        nextGreaterElement_getAt 0 xs =
        if xs = [] then (&0:int) else HD xs) /\
     (!i:num. !xs:int list.
        nextGreaterElement_getAt (SUC i) xs =
        if xs = [] then (&0:int)
        else nextGreaterElement_getAt i (TL xs))`;;

let nextGreaterElement_processStack =
  new_recursive_definition list_RECURSION
    `(!nums2:int list. !currentValue:int.
      !map:(int#int)list.
        nextGreaterElement_processStack
          nums2 currentValue ([]:num list) map =
        (([]:num list),map)) /\
     (!topIndex:num. !rest:num list. !nums2:int list.
      !currentValue:int. !map:(int#int)list.
        nextGreaterElement_processStack
          nums2 currentValue (CONS topIndex rest) map =
        let topValue =
          nextGreaterElement_getAt topIndex nums2 in
        if currentValue > topValue then
          nextGreaterElement_processStack
            nums2 currentValue rest
            (CONS (topValue,currentValue) map)
        else
          (CONS topIndex rest,map))`;;

let nextGreaterElement_finishMap =
  new_recursive_definition list_RECURSION
    `(!nums2:int list. !map:(int#int)list.
        nextGreaterElement_finishMap
          nums2 ([]:num list) map = map) /\
     (!pos:num. !rest:num list. !nums2:int list.
      !map:(int#int)list.
        nextGreaterElement_finishMap
          nums2 (CONS pos rest) map =
        nextGreaterElement_finishMap nums2 rest
          (CONS
            (nextGreaterElement_getAt pos nums2,-- &1)
            map))`;;

let nextGreaterElement_mapLoop =
  new_recursive_definition list_RECURSION
    `(!nums2:int list. !index:num. !stack:num list.
      !map:(int#int)list.
        nextGreaterElement_mapLoop
          nums2 ([]:int list) index stack map =
        nextGreaterElement_finishMap nums2 stack map) /\
     (!currentValue:int. !remaining:int list.
      !nums2:int list. !index:num. !stack:num list.
      !map:(int#int)list.
        nextGreaterElement_mapLoop
          nums2 (CONS currentValue remaining)
          index stack map =
        let processed =
          nextGreaterElement_processStack
            nums2 currentValue stack map in
        nextGreaterElement_mapLoop
          nums2 remaining (index + 1)
          (CONS index (FST processed))
          (SND processed))`;;

let nextGreaterElement_buildNextGreaterMap = new_definition
  `nextGreaterElement_buildNextGreaterMap
      (nums2:int list) =
     nextGreaterElement_mapLoop
       nums2 nums2 0 ([]:num list) ([]:(int#int)list)`;;

let nextGreaterElement_findInMap =
  new_recursive_definition list_RECURSION
    `(!value:int.
        nextGreaterElement_findInMap
          ([]:(int#int)list) value = (-- &1:int)) /\
     (!entry:int#int. !rest:(int#int)list. !value:int.
        nextGreaterElement_findInMap
          (CONS entry rest) value =
        if FST entry = value then SND entry
        else nextGreaterElement_findInMap rest value)`;;

let nextGreaterElement_buildResult =
  new_recursive_definition list_RECURSION
    `(!map:(int#int)list.
        nextGreaterElement_buildResult
          map ([]:int list) = []) /\
     (!value:int. !rest:int list. !map:(int#int)list.
        nextGreaterElement_buildResult
          map (CONS value rest) =
        CONS
          (nextGreaterElement_findInMap map value)
          (nextGreaterElement_buildResult map rest))`;;

let nextGreaterElement = new_definition
  `nextGreaterElement
      (nums1:int list) (nums2:int list) =
     let nextMap =
       nextGreaterElement_buildNextGreaterMap nums2 in
     nextGreaterElement_buildResult nextMap nums1`;;

let nextGreaterElement_findGreater =
  new_recursive_definition list_RECURSION
    `(!value:int.
        nextGreaterElement_findGreater
          value ([]:int list) = (NONE:int option)) /\
     (!x:int. !xs:int list. !value:int.
        nextGreaterElement_findGreater
          value (CONS x xs) =
        if x > value then SOME x
        else nextGreaterElement_findGreater value xs)`;;

let nextGreaterElement_optionMatches = new_definition
  `nextGreaterElement_optionMatches
      (candidate:int option) (resultValue:int) <=>
     (candidate = NONE /\ resultValue = -- &1) \/
     (?x:int. candidate = SOME x /\ resultValue = x)`;;

let nextGreaterElement_matchesValue =
  new_recursive_definition list_RECURSION
    `(!value:int. !resultValue:int.
        nextGreaterElement_matchesValue
          value resultValue ([]:int list) <=> F) /\
     (!x:int. !xs:int list. !value:int. !resultValue:int.
        nextGreaterElement_matchesValue
          value resultValue (CONS x xs) <=>
        if x = value then
          nextGreaterElement_optionMatches
            (nextGreaterElement_findGreater value xs)
            resultValue
        else
          nextGreaterElement_matchesValue
            value resultValue xs)`;;

let nextGreaterElement_matchesResult =
  new_recursive_definition list_RECURSION
    `(!nums2:int list. !result:int list.
        nextGreaterElement_matchesResult
          nums2 ([]:int list) result <=> T) /\
     (!value:int. !values:int list. !nums2:int list.
      !result:int list.
        nextGreaterElement_matchesResult
          nums2 (CONS value values) result <=>
        ~(result = []) /\
        nextGreaterElement_matchesValue
          value (HD result) nums2 /\
        nextGreaterElement_matchesResult
          nums2 values (TL result))`;;

let nextGreaterElement_postcond = new_definition
  `nextGreaterElement_postcond
      (nums1:int list) (nums2:int list)
      (result:int list) <=>
     LENGTH result = LENGTH nums1 /\
     nextGreaterElement_matchesResult nums2 nums1 result /\
     ALL
       (\value:int.
          value = -- &1 \/ MEM value nums2)
       result`;;

let nextGreaterElement_spec_satisfied =
  `!nums1:int list. !nums2:int list.
     nextGreaterElement_precond nums1 nums2
     ==> nextGreaterElement_postcond
           nums1 nums2
           (nextGreaterElement nums1 nums2)`;;
