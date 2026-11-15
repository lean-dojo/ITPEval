(*
  Statement-only formalization of VERINA corpus artifact verina_basic_64
  (verina__hol-light__verina_basic_64), catalog title "insert": an executable
  three-pass insertion of a bounded character-array prefix into another
  bounded character-array prefix, together with its bounds precondition,
  exact layout postcondition, and correctness proposition. This file contains
  no proof.
*)

let insert_validChar = new_definition
  `insert_validChar (c:num) <=>
     c < 55296 \/ (57343 < c /\ c < 1114112)`;;

let insert_array = new_definition
  `insert_array (xs:num list) <=>
     ALL insert_validChar xs`;;

let insert_precond = new_definition
  `insert_precond
      (oline:num list) (l:num) (nl:num list) (p:num) (atPos:num) <=>
     l <= LENGTH oline /\
     p <= LENGTH nl /\
     atPos <= l`;;

let insert_getDefault = new_definition
  `insert_getDefault (xs:num list) (i:num) =
     if i < LENGTH xs then EL i xs else 0`;;

let insert_setAt =
  new_recursive_definition list_RECURSION
    `(!i:num. !value:num.
        insert_setAt ([]:num list) i value = []) /\
     (!x:num. !xs:num list. !i:num. !value:num.
        insert_setAt (CONS x xs) i value =
        if i = 0 then CONS value xs
        else CONS x (insert_setAt xs (PRE i) value))`;;

let insert_prefixLoop =
  new_recursive_definition num_RECURSION
    `(!oline:num list. !atPos i:num. !result:num list.
        insert_prefixLoop 0 oline atPos i result = result) /\
     (!fuel:num. !oline:num list. !atPos i:num. !result:num list.
        insert_prefixLoop (SUC fuel) oline atPos i result =
        let next =
          if i < atPos then
            insert_setAt result i (insert_getDefault oline i)
          else
            result in
        insert_prefixLoop fuel oline atPos (SUC i) next)`;;

let insert_newLoop =
  new_recursive_definition num_RECURSION
    `(!nl:num list. !atPos i:num. !result:num list.
        insert_newLoop 0 nl atPos i result = result) /\
     (!fuel:num. !nl:num list. !atPos i:num. !result:num list.
        insert_newLoop (SUC fuel) nl atPos i result =
        let next =
          insert_setAt result (atPos + i) (insert_getDefault nl i) in
        insert_newLoop fuel nl atPos (SUC i) next)`;;

let insert_suffixLoop =
  new_recursive_definition num_RECURSION
    `(!oline:num list. !p atPos i:num. !result:num list.
        insert_suffixLoop 0 oline p atPos i result = result) /\
     (!fuel:num. !oline:num list. !p atPos i:num. !result:num list.
        insert_suffixLoop (SUC fuel) oline p atPos i result =
        let next =
          if atPos <= i then
            insert_setAt result (i + p) (insert_getDefault oline i)
          else
            result in
        insert_suffixLoop fuel oline p atPos (SUC i) next)`;;

let insert = new_definition
  `insert
      (oline:num list) (l:num) (nl:num list) (p:num) (atPos:num) =
     let result0 = REPLICATE (l + p) (32:num) in
     let result1 = insert_prefixLoop l oline atPos 0 result0 in
     let result2 = insert_newLoop p nl atPos 0 result1 in
     insert_suffixLoop l oline p atPos 0 result2`;;

let insert_postcond = new_definition
  `insert_postcond
      (oline:num list) (l:num) (nl:num list) (p:num) (atPos:num)
      (result:num list) <=>
     LENGTH result = l + p /\
     (!i:num.
        i < p
        ==> insert_getDefault result (atPos + i) =
            insert_getDefault nl i) /\
     (!i:num.
        i < atPos
        ==> insert_getDefault result i =
            insert_getDefault oline i) /\
     (!i:num.
        i < l - atPos
        ==> insert_getDefault result (atPos + p + i) =
            insert_getDefault oline (atPos + i))`;;

let insert_spec_satisfied =
  `!oline:num list. !l:num. !nl:num list. !p atPos:num.
     insert_array oline /\
     insert_array nl /\
     insert_precond oline l nl p atPos
     ==> insert_postcond
           oline l nl p atPos
           (insert oline l nl p atPos)`;;
