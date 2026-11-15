(*
  Statement-only formalization of VERINA corpus artifact verina_basic_34
  (verina__hol-light__verina_basic_34), catalog title "findEvenNumbers": an
  executable left fold extracts exactly the even integers from an array while
  preserving multiplicities and input order, together with its total
  correctness contract. This file contains no proof.
*)

let isEven = new_definition
  `isEven (n:int) <=>
     n rem (&2:int) = (&0:int)`;;

let findEvenNumbers_precond = new_definition
  `findEvenNumbers_precond (arr:int list) <=> T`;;

let findEvenNumbers_fold =
  new_recursive_definition list_RECURSION
    `(!acc:int list.
        findEvenNumbers_fold ([]:int list) acc = acc) /\
     (!x:int. !xs:int list. !acc:int list.
        findEvenNumbers_fold (CONS x xs) acc =
        findEvenNumbers_fold xs
          (if isEven x then APPEND acc [x] else acc))`;;

let findEvenNumbers = new_definition
  `findEvenNumbers (arr:int list) =
     findEvenNumbers_fold arr []`;;

let findEvenNumbers_count = new_definition
  `findEvenNumbers_count (value:int) (xs:int list) =
     LENGTH (FILTER (\x:int. x = value) xs)`;;

let findEvenNumbers_idxOf =
  new_recursive_definition list_RECURSION
    `(findEvenNumbers_idxOf (value:int) [] = 0) /\
     (!x:int. !xs:int list. !value:int.
        findEvenNumbers_idxOf value (CONS x xs) =
        if x = value then 0
        else SUC (findEvenNumbers_idxOf value xs))`;;

let findEvenNumbers_postcond = new_definition
  `findEvenNumbers_postcond
      (arr:int list) (result:int list) <=>
     ALL
       (\x:int.
          isEven x /\
          MEM x arr /\
          findEvenNumbers_count x result =
            findEvenNumbers_count x arr)
       result /\
     ALL
       (\x:int. isEven x ==> MEM x result)
       arr /\
     ALL
       (\x:int.
          ALL
            (\y:int.
               isEven x
               ==> isEven y
               ==> findEvenNumbers_idxOf x arr <=
                   findEvenNumbers_idxOf y arr
               ==> findEvenNumbers_idxOf x result <=
                   findEvenNumbers_idxOf y result)
            arr)
       arr`;;

let findEvenNumbers_spec_satisfied =
  `!arr:int list.
     findEvenNumbers_precond arr
     ==> findEvenNumbers_postcond
           arr (findEvenNumbers arr)`;;
