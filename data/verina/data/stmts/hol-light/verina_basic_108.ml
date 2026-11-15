(*
  Statement-only formalization of VERINA corpus artifact verina_basic_108,
  catalog title "below_zero": an executable cumulative-sum construction
  returns all integer partial sums and a Boolean indicating whether a
  post-initial partial sum is negative, together with its total precondition
  and complete correctness contract. This file contains no proof.
*)

let below_zero_precond = new_definition
  `below_zero_precond (operations:int list) <=> T`;;

let below_zero_lastDefault =
  new_recursive_definition list_RECURSION
    `(below_zero_lastDefault ([]:int list) = (&0:int)) /\
     (!x:int. !xs:int list.
        below_zero_lastDefault (CONS x xs) =
        if xs = [] then x else below_zero_lastDefault xs)`;;

let below_zero_buildFold =
  new_recursive_definition list_RECURSION
    `(!acc:int list.
        below_zero_buildFold ([]:int list) acc = acc) /\
     (!op:int. !operations:int list. !acc:int list.
        below_zero_buildFold (CONS op operations) acc =
        below_zero_buildFold operations
          (APPEND acc
            (CONS (below_zero_lastDefault acc + op) [])))`;;

let buildS = new_definition
  `buildS (operations:int list) =
     below_zero_buildFold operations (CONS (&0:int) [])`;;

let below_zero_checkNegative =
  new_recursive_definition list_RECURSION
    `(below_zero_checkNegative ([]:int list) <=> F) /\
     (!x:int. !xs:int list.
        below_zero_checkNegative (CONS x xs) <=>
        if x < &0 then T else below_zero_checkNegative xs)`;;

let below_zero = new_definition
  `below_zero (operations:int list) =
     let s = buildS operations in
     let result = below_zero_checkNegative s in
     (s,result)`;;

let below_zero_getOption = new_definition
  `below_zero_getOption (xs:int list) (i:num) =
     if i < LENGTH xs then SOME (EL i xs)
     else (NONE:int option)`;;

let below_zero_getDefault = new_definition
  `below_zero_getDefault (xs:int list) (i:num) =
     if i < LENGTH xs then EL i xs else (&0:int)`;;

let below_zero_postcond = new_definition
  `below_zero_postcond
      (operations:int list) (output:(int list)#bool) <=>
     let s = FST output in
     let result = SND output in
     LENGTH s = LENGTH operations + 1 /\
     below_zero_getOption s 0 = SOME (&0:int) /\
     (!i:num.
        i < LENGTH s - 1
        ==> below_zero_getOption s (i + 1) =
            SOME
              (below_zero_getDefault s i +
               below_zero_getDefault operations i)) /\
     (result = T
      ==> (?i:num.
             i < LENGTH operations /\
             below_zero_getDefault s (i + 1) < &0)) /\
     (result = F
      ==> ALL (\x:int. &0 <= x) s)`;;

let below_zero_spec_satisfied =
  `!operations:int list.
     below_zero_precond operations
     ==> below_zero_postcond operations (below_zero operations)`;;
