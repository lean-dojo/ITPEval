(*
  Statement-only formalization of VERINA corpus artifact verina_basic_44
  (verina__hol-light__verina_basic_44), catalog title "isOddAtIndexOdd": an
  executable indexed scan decides whether every odd array index contains an
  odd integer, together with its total precondition and exact Boolean
  correctness contract. This file contains no proof.
*)

let isOddAtIndexOdd_isOdd = new_definition
  `isOddAtIndexOdd_isOdd (n:int) <=>
     n rem (&2:int) = (&1:int)`;;

let isOddAtIndexOdd_precond = new_definition
  `isOddAtIndexOdd_precond (a:int list) <=> T`;;

let isOddAtIndexOdd_scan =
  new_recursive_definition list_RECURSION
    `(!i:num.
        isOddAtIndexOdd_scan ([]:int list) i = T) /\
     (!x:int. !xs:int list. !i:num.
        isOddAtIndexOdd_scan (CONS x xs) i =
        if isOddAtIndexOdd_isOdd (&i) then
          if isOddAtIndexOdd_isOdd x then
            isOddAtIndexOdd_scan xs (SUC i)
          else
            F
        else
          isOddAtIndexOdd_scan xs (SUC i))`;;

let isOddAtIndexOdd = new_definition
  `isOddAtIndexOdd (a:int list) =
     isOddAtIndexOdd_scan a 0`;;

let isOddAtIndexOdd_postcond = new_definition
  `isOddAtIndexOdd_postcond
      (a:int list) (result:bool) <=>
     (result <=>
      !i:num.
        i < LENGTH a
        ==> isOddAtIndexOdd_isOdd (&i)
        ==> isOddAtIndexOdd_isOdd (EL i a))`;;

let isOddAtIndexOdd_spec_satisfied =
  `!a:int list.
     isOddAtIndexOdd_precond a
     ==> isOddAtIndexOdd_postcond
           a (isOddAtIndexOdd a)`;;
