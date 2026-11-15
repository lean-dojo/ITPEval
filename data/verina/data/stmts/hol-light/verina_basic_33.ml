(*
  Statement-only formalization of VERINA corpus artifact verina_basic_33
  (verina__hol-light__verina_basic_33), catalog title
  "smallestMissingNumber": an executable recursive scan returns the least
  natural number absent from a nondecreasing list, together with its absence
  and minimality correctness contract. This file contains no proof.
*)

let smallestMissingNumber_precond = new_definition
  `smallestMissingNumber_precond (s:num list) <=>
     PAIRWISE (\x y:num. x <= y) s`;;

let smallestMissingNumber_findMissing =
  new_recursive_definition list_RECURSION
    `(!v:num.
        smallestMissingNumber_findMissing v ([]:num list) = v) /\
     (!x:num. !xs:num list. !v:num.
        smallestMissingNumber_findMissing v (CONS x xs) =
        if x > v then
          v
        else if x = v then
          smallestMissingNumber_findMissing (v + 1) xs
        else
          smallestMissingNumber_findMissing v xs)`;;

let smallestMissingNumber = new_definition
  `smallestMissingNumber (s:num list) =
     smallestMissingNumber_findMissing 0 s`;;

let smallestMissingNumber_postcond = new_definition
  `smallestMissingNumber_postcond
      (s:num list) (result:num) <=>
     ~(MEM result s) /\
     (!k:num. k < result ==> MEM k s)`;;

let smallestMissingNumber_spec_satisfied =
  `!s:num list.
     smallestMissingNumber_precond s
     ==> smallestMissingNumber_postcond
           s (smallestMissingNumber s)`;;
