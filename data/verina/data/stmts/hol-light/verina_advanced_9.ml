(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_9
  (verina__hol-light__verina_advanced_9), catalog title
  "countSumDivisibleBy": an executable scan counts the natural numbers below
  n whose decimal digit sum is divisible by a positive d, together with its
  precondition and postcondition correctness contract. This file contains no
  proof.
*)

let sumOfDigits_go = define
  `sumOfDigits_go(n,acc) =
     if n = 0 then acc
     else sumOfDigits_go(n DIV 10,acc + n MOD 10)`;;

let sumOfDigits = new_definition
  `sumOfDigits (x:num) = sumOfDigits_go(x,0)`;;

let countSumDivisibleBy_precond = new_definition
  `countSumDivisibleBy_precond (n:num) (d:num) <=>
     0 < d`;;

let isSumDivisibleBy = new_definition
  `isSumDivisibleBy (x:num) (d:num) <=>
     sumOfDigits x MOD d = 0`;;

let countSumDivisibleBy_go =
  new_recursive_definition num_RECURSION
    `(!d:num. !acc:num.
        countSumDivisibleBy_go 0 d acc = acc) /\
     (!i:num. !d:num. !acc:num.
        countSumDivisibleBy_go (SUC i) d acc =
        let acc' =
          if isSumDivisibleBy i d then acc + 1 else acc in
        countSumDivisibleBy_go i d acc')`;;

let countSumDivisibleBy = new_definition
  `countSumDivisibleBy (n:num) (d:num) =
     countSumDivisibleBy_go n d 0`;;

let countSumDivisibleBy_range =
  new_recursive_definition num_RECURSION
    `(countSumDivisibleBy_range 0 = []) /\
     (!n:num.
        countSumDivisibleBy_range (SUC n) =
        APPEND (countSumDivisibleBy_range n) (CONS n []))`;;

let countSumDivisibleBy_postcond = new_definition
  `countSumDivisibleBy_postcond
      (n:num) (d:num) (result:num) <=>
     let expected =
       LENGTH
         (FILTER
           (\x:num. x < n /\ sumOfDigits x MOD d = 0)
           (countSumDivisibleBy_range n)) in
     expected - result = 0 /\
     result <= expected`;;

let countSumDivisibleBy_spec_satisfied =
  `!n:num. !d:num.
     countSumDivisibleBy_precond n d
     ==> countSumDivisibleBy_postcond
           n d (countSumDivisibleBy n d)`;;
