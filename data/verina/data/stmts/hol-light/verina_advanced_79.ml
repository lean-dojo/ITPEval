(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_79,
  catalog title "twoSum": a deterministic nested scan of an integer list
  returns the lexicographically first increasing index pair whose values sum
  to the target, or no pair when none exists, with its correctness contract.
  This file contains no proof.
*)

let twoSum_precond = new_definition
  `twoSum_precond (nums:int list) (target:int) <=> T`;;

let twoSum_inner =
  new_recursive_definition list_RECURSION
    `(!x:int. !target:int. !j:num.
        twoSum_inner ([]:int list) x target j =
        (NONE:num option)) /\
     (!y:int. !ys:int list. !x:int. !target:int. !j:num.
        twoSum_inner (CONS y ys) x target j =
        if x + y = target then SOME j
        else twoSum_inner ys x target (j + 1))`;;

let twoSum_optionValue =
  new_recursive_definition option_RECURSION
    `(twoSum_optionValue (NONE:num option) = 0) /\
     (!j:num. twoSum_optionValue (SOME j) = j)`;;

let twoSum_outer =
  new_recursive_definition list_RECURSION
    `(!target:int. !i:num.
        twoSum_outer ([]:int list) target i =
        (NONE:(num#num) option)) /\
     (!x:int. !xs:int list. !target:int. !i:num.
        twoSum_outer (CONS x xs) target i =
        let candidate = twoSum_inner xs x target (i + 1) in
        if candidate = NONE then
          twoSum_outer xs target (i + 1)
        else
          SOME (i,twoSum_optionValue candidate))`;;

let twoSum = new_definition
  `twoSum (nums:int list) (target:int) =
     twoSum_outer nums target 0`;;

let twoSum_postcond_by_result =
  new_recursive_definition option_RECURSION
    `(!nums:int list. !target:int.
        twoSum_postcond_by_result
          (NONE:(num#num) option) nums target <=>
        PAIRWISE
          (\x y:int. ~(x + y = target))
          nums) /\
     (!result:num#num. !nums:int list. !target:int.
        twoSum_postcond_by_result
          (SOME result) nums target <=>
        let i = FST result in
        let j = SND result in
        i < j /\
        j < LENGTH nums /\
        EL i nums + EL j nums = target /\
        (!i':num. !j':num.
           i' < i /\ i' < j' /\ j' < LENGTH nums
           ==> ~(EL i' nums + EL j' nums = target)) /\
        (!j':num.
           i < j' /\ j' < j
           ==> ~(EL i nums + EL j' nums = target)))`;;

let twoSum_postcond = new_definition
  `twoSum_postcond
      (nums:int list) (target:int) (result:(num#num) option) <=>
     twoSum_postcond_by_result result nums target`;;

let twoSum_spec_satisfied =
  `!nums:int list. !target:int.
     twoSum_precond nums target
     ==> twoSum_postcond nums target (twoSum nums target)`;;
