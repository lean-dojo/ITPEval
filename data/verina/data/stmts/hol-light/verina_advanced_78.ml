(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_78,
  catalog title "twoSum": an exact executable complement scan returns the
  unique pair of increasing indices whose integer-list values sum to the
  target, together with its correctness contract. This file contains no proof.
*)

let twoSum_pairwiseSums =
  new_recursive_definition list_RECURSION
    `(twoSum_pairwiseSums ([]:int list) = []) /\
     (!x:int. !xs:int list.
        twoSum_pairwiseSums (CONS x xs) =
        APPEND
          (MAP (\y:int. x + y) xs)
          (twoSum_pairwiseSums xs))`;;

let twoSum_count = new_definition
  `twoSum_count (target:int) (sums:int list) =
     LENGTH (FILTER (\value:int. value = target) sums)`;;

let twoSum_precond = new_definition
  `twoSum_precond (nums:int list) (target:int) <=>
     LENGTH nums > 1 /\
     twoSum_count target (twoSum_pairwiseSums nums) = 1`;;

let findComplement_aux =
  new_recursive_definition list_RECURSION
    `(!target:int. !i:num. !x:int. !j:num.
        findComplement_aux ([]:int list) target i x j =
        (NONE:num option)) /\
     (!y:int. !ys:int list. !target:int. !i:num. !x:int. !j:num.
        findComplement_aux (CONS y ys) target i x j =
        if x + y = target then SOME (i + j + 1)
        else findComplement_aux ys target i x (j + 1))`;;

let findComplement = new_definition
  `findComplement
      (nums:int list) (target:int) (i:num) (x:int) =
     findComplement_aux nums target i x 0`;;

let twoSum_optionValue =
  new_recursive_definition option_RECURSION
    `(twoSum_optionValue (NONE:num option) = 0) /\
     (!j:num. twoSum_optionValue (SOME j) = j)`;;

let twoSumAux =
  new_recursive_definition list_RECURSION
    `(!target:int. !i:num.
        twoSumAux ([]:int list) target i = ((0:num),(0:num))) /\
     (!x:int. !xs:int list. !target:int. !i:num.
        twoSumAux (CONS x xs) target i =
        let candidate = findComplement xs target i x in
        if candidate = NONE then
          twoSumAux xs target (i + 1)
        else
          (i,twoSum_optionValue candidate))`;;

let twoSum = new_definition
  `twoSum (nums:int list) (target:int) =
     twoSumAux nums target 0`;;

let twoSum_postcond = new_definition
  `twoSum_postcond
      (nums:int list) (target:int) (result:num#num) <=>
     let i = FST result in
     let j = SND result in
     i < j /\
     i < LENGTH nums /\
     j < LENGTH nums /\
     EL i nums + EL j nums = target`;;

let twoSum_spec_satisfied =
  `!nums:int list. !target:int.
     twoSum_precond nums target
     ==> twoSum_postcond
           nums target (twoSum nums target)`;;
