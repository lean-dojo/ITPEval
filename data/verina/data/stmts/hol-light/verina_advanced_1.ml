(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_1,
  catalog title "FindSingleNumber": an executable list scan returns the sole
  integer occurring once when every listed integer occurs once or twice and
  exactly one listed occurrence count is one. This file contains no proof.
*)

let filterlist = new_recursive_definition list_RECURSION
  `(filterlist (x:int) [] = []) /\
   (!y:int. !ys:int list.
      filterlist x (CONS y ys) =
        if y = x then CONS y (filterlist x ys)
        else filterlist x ys)`;;

let FindSingleNumber_precond = new_definition
  `FindSingleNumber_precond (nums:int list) <=>
     let numsCount =
       MAP (\x:int. LENGTH (filterlist x nums)) nums in
     ALL (\count:num. count = 1 \/ count = 2) numsCount /\
     LENGTH (FILTER (\count:num. count = 1) numsCount) = 1`;;

let findUnique = new_recursive_definition list_RECURSION
  `(findUnique (nums:int list) [] = (&0:int)) /\
   (!x:int. !xs:int list.
      findUnique nums (CONS x xs) =
        if LENGTH (filterlist x nums) = 1
        then x
        else findUnique nums xs)`;;

let FindSingleNumber = new_definition
  `FindSingleNumber (nums:int list) = findUnique nums nums`;;

let FindSingleNumber_postcond = new_definition
  `FindSingleNumber_postcond (nums:int list) (result:int) <=>
     0 < LENGTH nums /\
     LENGTH (filterlist result nums) = 1 /\
     (!x:int.
        MEM x nums
        ==> x = result \/ LENGTH (filterlist x nums) = 2)`;;

let FindSingleNumber_spec_satisfied =
  `!nums:int list.
     FindSingleNumber_precond nums
     ==> FindSingleNumber_postcond nums (FindSingleNumber nums)`;;
