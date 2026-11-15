(*
  Statement-only formalization of VERINA corpus artifact verina_basic_102,
  catalog title "twoSum": an executable nested scan returns the
  lexicographically first pair of increasing indices whose integer-list
  values sum to the target, together with its correctness contract. This file
  contains no proof.
*)

let twoSum_precond = new_definition
  `twoSum_precond (nums:int list) (target:int) <=>
     LENGTH nums > 1 /\
     ~(PAIRWISE (\a b:int. ~(a + b = target)) nums)`;;

let twoSum_findLater =
  new_recursive_definition list_RECURSION
    `(!target:int. !i:num. !x:int. !offset:num.
        twoSum_findLater ([]:int list) target i x offset =
        (NONE:num option)) /\
     (!y:int. !ys:int list. !target:int. !i:num. !x:int. !offset:num.
        twoSum_findLater (CONS y ys) target i x offset =
        if x + y = target then SOME (i + offset + 1)
        else twoSum_findLater ys target i x (offset + 1))`;;

let twoSum_optionValue =
  new_recursive_definition option_RECURSION
    `(twoSum_optionValue (NONE:num option) = 0) /\
     (!j:num. twoSum_optionValue (SOME j) = j)`;;

let twoSum_outer =
  new_recursive_definition list_RECURSION
    `(!target:int. !i:num.
        twoSum_outer ([]:int list) target i = ((0:num),(0:num))) /\
     (!x:int. !xs:int list. !target:int. !i:num.
        twoSum_outer (CONS x xs) target i =
        let candidate = twoSum_findLater xs target i x 0 in
        if candidate = NONE then
          twoSum_outer xs target (i + 1)
        else
          (i,twoSum_optionValue candidate))`;;

let twoSum = new_definition
  `twoSum (nums:int list) (target:int) =
     twoSum_outer nums target 0`;;

let twoSum_postcond = new_definition
  `twoSum_postcond
      (nums:int list) (target:int) (result:num#num) <=>
     let i = FST result in
     let j = SND result in
     i < j /\
     j < LENGTH nums /\
     EL i nums + EL j nums = target /\
     (!i':num.
        i' < i
        ==> (!k:num.
               i' < k /\ k < LENGTH nums
               ==> ~(EL i' nums + EL k nums = target))) /\
     (!k:num.
        i < k /\ k < j
        ==> ~(EL i nums + EL k nums = target))`;;

let twoSum_spec_satisfied =
  `!nums:int list. !target:int.
     twoSum_precond nums target
     ==> twoSum_postcond nums target (twoSum nums target)`;;
