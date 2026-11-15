(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_43,
  catalog title "maxStrength": an executable bitmask enumeration computes the
  greatest product of a nonempty subset of a nonempty integer list, and the
  postcondition characterizes that maximum via nonempty sublists. This file
  contains no proof.
*)

let maxStrength_precond = new_definition
  `maxStrength_precond (nums:int list) <=>
     ~(nums = [])`;;

let maxStrength_range =
  new_recursive_definition num_RECURSION
    `(maxStrength_range 0 = []) /\
     (!n:num.
        maxStrength_range (SUC n) =
        APPEND (maxStrength_range n) (CONS n []))`;;

let maxStrength_get =
  new_recursive_definition num_RECURSION
    `(!nums:int list.
        maxStrength_get 0 nums =
        if nums = [] then (&0:int) else HD nums) /\
     (!i:num. !nums:int list.
        maxStrength_get (SUC i) nums =
        if nums = [] then (&0:int)
        else maxStrength_get i (TL nums))`;;

let maxStrength_select =
  new_recursive_definition list_RECURSION
    `(!nums:int list. !mask:num.
        maxStrength_select nums mask ([]:num list) = []) /\
     (!i:num. !indices:num list. !nums:int list. !mask:num.
        maxStrength_select nums mask (CONS i indices) =
        if (mask DIV (2 EXP i)) MOD 2 = 1 then
          CONS (maxStrength_get i nums)
            (maxStrength_select nums mask indices)
        else
          maxStrength_select nums mask indices)`;;

let maxStrength_powerSet = new_definition
  `maxStrength_powerSet (nums:int list) =
     MAP
       (\mask:num.
          maxStrength_select nums mask
            (maxStrength_range (LENGTH nums)))
       (maxStrength_range (2 EXP (LENGTH nums)))`;;

let maxStrength_productFold =
  new_recursive_definition list_RECURSION
    `(!acc:int.
        maxStrength_productFold ([]:int list) acc = acc) /\
     (!x:int. !xs:int list. !acc:int.
        maxStrength_productFold (CONS x xs) acc =
        maxStrength_productFold xs (acc * x))`;;

let maxStrength_product = new_definition
  `maxStrength_product (xs:int list) =
     maxStrength_productFold xs (&1:int)`;;

let maxStrength_maxFold =
  new_recursive_definition list_RECURSION
    `(!acc:int.
        maxStrength_maxFold ([]:int list) acc = acc) /\
     (!x:int. !xs:int list. !acc:int.
        maxStrength_maxFold (CONS x xs) acc =
        maxStrength_maxFold xs
          (if acc <= x then x else acc))`;;

let maxStrength_maximum = new_definition
  `maxStrength_maximum (products:int list) =
     if products = [] then (-- &1000000:int)
     else maxStrength_maxFold (TL products) (HD products)`;;

let maxStrength = new_definition
  `maxStrength (nums:int list) =
     let subsets = maxStrength_powerSet nums in
     let nonEmpty = FILTER (\subset:int list. ~(subset = [])) subsets in
     let products = MAP maxStrength_product nonEmpty in
     maxStrength_maximum products`;;

let maxStrength_sublists =
  new_recursive_definition list_RECURSION
    `(maxStrength_sublists ([]:int list) = CONS [] []) /\
     (!x:int. !xs:int list.
        maxStrength_sublists (CONS x xs) =
        let rest = maxStrength_sublists xs in
        APPEND rest
          (MAP (\sub:int list. CONS x sub) rest))`;;

let maxStrength_postcond = new_definition
  `maxStrength_postcond (nums:int list) (result:int) <=>
     let sublists =
       FILTER
         (\sub:int list. ~(sub = []))
         (maxStrength_sublists nums) in
     let products = MAP maxStrength_product sublists in
     MEM result products /\
     ALL (\p:int. p <= result) products`;;

let maxStrength_spec_satisfied =
  `!nums:int list.
     maxStrength_precond nums
     ==> maxStrength_postcond nums (maxStrength nums)`;;
