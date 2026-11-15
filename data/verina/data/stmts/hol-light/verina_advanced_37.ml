(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_37,
  catalog title "majorityElement": executable insertion sorting of an integer
  list followed by middle-element selection returns its majority element under
  the nonempty-majority precondition, with the full occurrence postcondition.
  This file contains no proof.
*)

let majorityElement_count =
  new_recursive_definition list_RECURSION
    `(majorityElement_count (value:int) ([]:int list) = 0) /\
     (!x:int. !xs:int list. !value:int.
        majorityElement_count value (CONS x xs) =
        if x = value
        then SUC (majorityElement_count value xs)
        else majorityElement_count value xs)`;;

let majorityElement_precond = new_definition
  `majorityElement_precond (nums:int list) <=>
     0 < LENGTH nums /\
     EX
       (\x:int.
          majorityElement_count x nums > LENGTH nums DIV 2)
       nums`;;

let majorityElement_insert =
  new_recursive_definition list_RECURSION
    `(majorityElement_insert (x:int) ([]:int list) = CONS x []) /\
     (!h:int. !t:int list. !x:int.
        majorityElement_insert x (CONS h t) =
        if x <= h
        then CONS x (CONS h t)
        else CONS h (majorityElement_insert x t))`;;

let majorityElement_insertionSort =
  new_recursive_definition list_RECURSION
    `(majorityElement_insertionSort ([]:int list) = []) /\
     (!h:int. !t:int list.
        majorityElement_insertionSort (CONS h t) =
        majorityElement_insert
          h (majorityElement_insertionSort t))`;;

let majorityElement_getAt =
  new_recursive_definition num_RECURSION
    `(!xs:int list.
        majorityElement_getAt 0 xs =
        if xs = [] then (&0:int) else HD xs) /\
     (!i:num. !xs:int list.
        majorityElement_getAt (SUC i) xs =
        if xs = [] then (&0:int)
        else majorityElement_getAt i (TL xs))`;;

let majorityElement = new_definition
  `majorityElement (nums:int list) =
     let sorted = majorityElement_insertionSort nums in
     let len = LENGTH sorted in
     let mid = len DIV 2 in
     majorityElement_getAt mid sorted`;;

let majorityElement_postcond = new_definition
  `majorityElement_postcond
      (nums:int list) (result:int) <=>
     let n = LENGTH nums in
     majorityElement_count result nums > n DIV 2 /\
     ALL
       (\x:int.
          x = result \/
          majorityElement_count x nums <= n DIV 2)
       nums`;;

let majorityElement_spec_satisfied =
  `!nums:int list.
     majorityElement_precond nums
     ==> majorityElement_postcond
           nums (majorityElement nums)`;;
