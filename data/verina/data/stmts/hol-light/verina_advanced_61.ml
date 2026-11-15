(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_61,
  catalog title "productExceptSelf": an executable prefix-and-suffix product
  computation returns, at each integer-list index, the product of every other
  entry, together with its total correctness contract. This file contains no
  proof.
*)

let productExceptSelf_precond = new_definition
  `productExceptSelf_precond (nums:int list) <=> T`;;

let productExceptSelf_lastDefault =
  new_recursive_definition list_RECURSION
    `(productExceptSelf_lastDefault ([]:int list) = (&0:int)) /\
     (!x:int. !xs:int list.
        productExceptSelf_lastDefault (CONS x xs) =
        if xs = [] then x
        else productExceptSelf_lastDefault xs)`;;

let productExceptSelf_prefixFold =
  new_recursive_definition list_RECURSION
    `(!acc:int list.
        productExceptSelf_prefixFold ([]:int list) acc = acc) /\
     (!x:int. !xs:int list. !acc:int list.
        productExceptSelf_prefixFold (CONS x xs) acc =
        productExceptSelf_prefixFold xs
          (APPEND acc
            (CONS
              (productExceptSelf_lastDefault acc * x)
              [])))`;;

let computepref = new_definition
  `computepref (nums:int list) =
     productExceptSelf_prefixFold nums (CONS (&1:int) [])`;;

let computeSuffix = new_definition
  `computeSuffix (nums:int list) =
     REVERSE (computepref (REVERSE nums))`;;

let productExceptSelf_range =
  new_recursive_definition num_RECURSION
    `(productExceptSelf_range 0 = []) /\
     (!n:num.
        productExceptSelf_range (SUC n) =
        APPEND (productExceptSelf_range n) (CONS n []))`;;

let productExceptSelf_getDefault = new_definition
  `productExceptSelf_getDefault
      (xs:int list) (index:num) =
     if index < LENGTH xs then EL index xs else (&0:int)`;;

let productExceptSelf = new_definition
  `productExceptSelf (nums:int list) =
     let n = LENGTH nums in
     if n = 0 then []
     else
       let pref = computepref nums in
       let suffix = computeSuffix nums in
       MAP
         (\i:num.
            productExceptSelf_getDefault pref i *
            productExceptSelf_getDefault suffix (i + 1))
         (productExceptSelf_range n)`;;

let productExceptSelf_myprod =
  new_recursive_definition list_RECURSION
    `(productExceptSelf_myprod ([]:int list) = (&1:int)) /\
     (!x:int. !xs:int list.
        productExceptSelf_myprod (CONS x xs) =
        x * productExceptSelf_myprod xs)`;;

let productExceptSelf_take =
  new_recursive_definition num_RECURSION
    `(!xs:int list.
        productExceptSelf_take 0 xs = []) /\
     (!n:num. !xs:int list.
        productExceptSelf_take (SUC n) xs =
        if xs = [] then []
        else
          CONS (HD xs)
            (productExceptSelf_take n (TL xs)))`;;

let productExceptSelf_drop =
  new_recursive_definition num_RECURSION
    `(!xs:int list.
        productExceptSelf_drop 0 xs = xs) /\
     (!n:num. !xs:int list.
        productExceptSelf_drop (SUC n) xs =
        if xs = [] then []
        else productExceptSelf_drop n (TL xs))`;;

let productExceptSelf_getOpt = new_definition
  `productExceptSelf_getOpt
      (xs:int list) (index:num) =
     if index < LENGTH xs then SOME (EL index xs)
     else (NONE:int option)`;;

let productExceptSelf_postcond = new_definition
  `productExceptSelf_postcond
      (nums:int list) (result:int list) <=>
     LENGTH nums = LENGTH result /\
     ALL
       (\i:num.
          productExceptSelf_getOpt result i =
          SOME
            (productExceptSelf_myprod
               (productExceptSelf_take i nums) *
             productExceptSelf_myprod
               (productExceptSelf_drop (i + 1) nums)))
       (productExceptSelf_range (LENGTH nums))`;;

let productExceptSelf_spec_satisfied =
  `!nums:int list.
     productExceptSelf_precond nums
     ==> productExceptSelf_postcond
           nums (productExceptSelf nums)`;;
