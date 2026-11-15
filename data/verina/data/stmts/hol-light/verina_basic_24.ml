(*
  Statement-only formalization of VERINA corpus artifact verina_basic_24,
  catalog title "firstEvenOddDifference": an executable left-to-right scan of
  an integer array returns the first even value minus the first odd value,
  together with its first-occurrence correctness contract. This file contains
  no proof.
*)

let firstEvenOddDifference_isEven = new_definition
  `firstEvenOddDifference_isEven (n:int) <=>
     n rem (&2:int) = (&0:int)`;;

let firstEvenOddDifference_isOdd = new_definition
  `firstEvenOddDifference_isOdd (n:int) <=>
     ~(n rem (&2:int) = (&0:int))`;;

let firstEvenOddDifference_precond = new_definition
  `firstEvenOddDifference_precond (a:int list) <=>
     LENGTH a > 1 /\
     (?x:int. MEM x a /\ firstEvenOddDifference_isEven x) /\
     (?x:int. MEM x a /\ firstEvenOddDifference_isOdd x)`;;

let firstEvenOddDifference_optionValue =
  new_recursive_definition option_RECURSION
    `(firstEvenOddDifference_optionValue
        (NONE:num option) = 0) /\
     (!index:num.
        firstEvenOddDifference_optionValue
          (SOME index) = index)`;;

let firstEvenOddDifference_findFirstEvenOdd =
  new_recursive_definition list_RECURSION
    `(!a:int list. !i:num.
      !firstEven:num option. !firstOdd:num option.
        firstEvenOddDifference_findFirstEvenOdd
          ([]:int list) a i firstEven firstOdd =
        (&0:int)) /\
     (!x:int. !xs:int list. !a:int list. !i:num.
      !firstEven:num option. !firstOdd:num option.
        firstEvenOddDifference_findFirstEvenOdd
          (CONS x xs) a i firstEven firstOdd =
        let newFirstEven =
          if firstEven = NONE /\
             firstEvenOddDifference_isEven x
          then SOME i
          else firstEven in
        let newFirstOdd =
          if firstOdd = NONE /\
             firstEvenOddDifference_isOdd x
          then SOME i
          else firstOdd in
        if ~(newFirstEven = NONE) /\ ~(newFirstOdd = NONE) then
          EL
            (firstEvenOddDifference_optionValue newFirstEven)
            a -
          EL
            (firstEvenOddDifference_optionValue newFirstOdd)
            a
        else
          firstEvenOddDifference_findFirstEvenOdd
            xs a (i + 1) newFirstEven newFirstOdd)`;;

let firstEvenOddDifference = new_definition
  `firstEvenOddDifference (a:int list) =
     firstEvenOddDifference_findFirstEvenOdd
       a a 0 NONE NONE`;;

let firstEvenOddDifference_postcond = new_definition
  `firstEvenOddDifference_postcond
      (a:int list) (result:int) <=>
     ?i:num. ?j:num.
       i < LENGTH a /\
       j < LENGTH a /\
       firstEvenOddDifference_isEven (EL i a) /\
       firstEvenOddDifference_isOdd (EL j a) /\
       result = EL i a - EL j a /\
       (!k:num.
          k < i
          ==> firstEvenOddDifference_isOdd (EL k a)) /\
       (!k:num.
          k < j
          ==> firstEvenOddDifference_isEven (EL k a))`;;

let firstEvenOddDifference_spec_satisfied =
  `!a:int list.
     firstEvenOddDifference_precond a
     ==> firstEvenOddDifference_postcond
           a (firstEvenOddDifference a)`;;
