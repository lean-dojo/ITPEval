(*
  Statement-only formalization of VERINA corpus artifact verina_basic_21,
  catalog title "isSublist": an executable bounded scan decides whether an
  integer list occurs contiguously within another integer list, with its total
  precondition and exact Boolean correctness contract. This file contains no
  proof.
*)

let isSublist_precond = new_definition
  `isSublist_precond
      (sub:int list) (main:int list) <=> T`;;

let isSublist_drop =
  new_recursive_definition num_RECURSION
    `(!xs:int list.
        isSublist_drop 0 xs = xs) /\
     (!n:num. !xs:int list.
        isSublist_drop (SUC n) xs =
        if xs = [] then []
        else isSublist_drop n (TL xs))`;;

let isSublist_take =
  new_recursive_definition num_RECURSION
    `(!xs:int list.
        isSublist_take 0 xs = []) /\
     (!n:num. !xs:int list.
        isSublist_take (SUC n) xs =
        if xs = [] then []
        else CONS (HD xs) (isSublist_take n (TL xs)))`;;

let isSublist_checkFuel =
  new_recursive_definition num_RECURSION
    `(!sub:int list. !main:int list. !i:num.
        isSublist_checkFuel 0 sub main i = F) /\
     (!fuel:num. !sub:int list. !main:int list. !i:num.
        isSublist_checkFuel (SUC fuel) sub main i =
        let subLen = LENGTH sub in
        let mainLen = LENGTH main in
        if i + subLen > mainLen then
          F
        else if
          sub =
            isSublist_take subLen
              (isSublist_drop i main)
        then
          T
        else if i + 1 <= mainLen then
          isSublist_checkFuel fuel sub main (i + 1)
        else
          F)`;;

let isSublist = new_definition
  `isSublist (sub:int list) (main:int list) =
     let subLen = LENGTH sub in
     let mainLen = LENGTH main in
     if subLen > mainLen then
       F
     else
       isSublist_checkFuel (SUC mainLen) sub main 0`;;

let isSublist_postcond = new_definition
  `isSublist_postcond
      (sub:int list) (main:int list) (result:bool) <=>
     ((?i:num.
         i + LENGTH sub <= LENGTH main /\
         sub =
           isSublist_take (LENGTH sub)
             (isSublist_drop i main)) <=>
      result)`;;

let isSublist_spec_satisfied =
  `!sub:int list. !main:int list.
     isSublist_precond sub main
     ==> isSublist_postcond
           sub main (isSublist sub main)`;;
