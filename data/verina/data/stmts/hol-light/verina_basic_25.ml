(*
  Statement-only formalization of VERINA corpus artifact verina_basic_25,
  catalog title "sumAndAverage": an executable natural-number summation returns
  its integer total and its IEEE-754 binary64 average, under the positive
  less-than-2^53 precondition and the closed-form correctness contract. Float
  values are represented by their 64-bit encodings, so NaNs, infinities,
  signed zeros, and Lean Float BEq remain observable. This file contains no
  proof.
*)

let sumAndAverage_float64 = new_definition
  `sumAndAverage_float64 (bits:num) <=>
     bits < 2 EXP 64`;;

let sumAndAverage_binary64Fraction = new_definition
  `sumAndAverage_binary64Fraction (bits:num) =
     bits MOD (2 EXP 52)`;;

let sumAndAverage_binary64Exponent = new_definition
  `sumAndAverage_binary64Exponent (bits:num) =
     (bits DIV (2 EXP 52)) MOD 2048`;;

let sumAndAverage_binary64FiniteNonnegative = new_definition
  `sumAndAverage_binary64FiniteNonnegative (bits:num) <=>
     sumAndAverage_float64 bits /\
     bits < 2 EXP 63 /\
     sumAndAverage_binary64Exponent bits < 2047`;;

let sumAndAverage_binary64Value = new_definition
  `sumAndAverage_binary64Value (bits:num) =
     let q = sumAndAverage_binary64Exponent bits in
     let f = sumAndAverage_binary64Fraction bits in
     if q = 0 then
       (&f:real) / &(2 EXP 1074)
     else if q <= 1075 then
       (&(2 EXP 52 + f):real) / &(2 EXP (1075 - q))
     else
       (&(2 EXP 52 + f):real) * &(2 EXP (q - 1075))`;;

let sumAndAverage_binary64Even = new_definition
  `sumAndAverage_binary64Even (bits:num) <=>
     bits MOD 2 = 0`;;

let sumAndAverage_binary64Rounds = new_definition
  `sumAndAverage_binary64Rounds (x:real) (rounded:num) <=>
     sumAndAverage_binary64FiniteNonnegative rounded /\
     (!candidate:num.
        sumAndAverage_binary64FiniteNonnegative candidate
        ==> abs (x - sumAndAverage_binary64Value rounded) <=
            abs (x - sumAndAverage_binary64Value candidate)) /\
     (!candidate:num.
        sumAndAverage_binary64FiniteNonnegative candidate /\
        ~(candidate = rounded) /\
        abs (x - sumAndAverage_binary64Value rounded) =
        abs (x - sumAndAverage_binary64Value candidate) /\
        sumAndAverage_binary64Even candidate
        ==> sumAndAverage_binary64Even rounded)`;;

let sumAndAverage_binary64Round = new_definition
  `sumAndAverage_binary64Round (x:real) =
     @rounded:num. sumAndAverage_binary64Rounds x rounded`;;

let sumAndAverage_natLog2 = new_definition
  `sumAndAverage_natLog2 (n:num) =
     @result:num.
       if n < 2 then
         result = 0
       else
         2 EXP result <= n /\ n < 2 EXP (result + 1)`;;

let sumAndAverage_floatScaleB = new_definition
  `sumAndAverage_floatScaleB (bits:num) (shift:num) =
     sumAndAverage_binary64Round
       (sumAndAverage_binary64Value bits * &(2 EXP shift))`;;

let sumAndAverage_floatOfNum = new_definition
  `sumAndAverage_floatOfNum (n:num) =
     let shift = sumAndAverage_natLog2 n - 63 in
     let mantissa = n DIV (2 EXP shift) in
     sumAndAverage_floatScaleB
       (sumAndAverage_binary64Round (&mantissa:real))
       shift`;;

let sumAndAverage_floatDiv = new_definition
  `sumAndAverage_floatDiv (x:num) (y:num) =
     sumAndAverage_binary64Round
       (sumAndAverage_binary64Value x /
        sumAndAverage_binary64Value y)`;;

let sumAndAverage_binary64IsNaN = new_definition
  `sumAndAverage_binary64IsNaN (bits:num) <=>
     sumAndAverage_float64 bits /\
     sumAndAverage_binary64Exponent bits = 2047 /\
     ~(sumAndAverage_binary64Fraction bits = 0)`;;

let sumAndAverage_binary64IsZero = new_definition
  `sumAndAverage_binary64IsZero (bits:num) <=>
     sumAndAverage_float64 bits /\
     sumAndAverage_binary64Exponent bits = 0 /\
     sumAndAverage_binary64Fraction bits = 0`;;

let sumAndAverage_floatBEq = new_definition
  `sumAndAverage_floatBEq (left:num) (right:num) <=>
     sumAndAverage_float64 left /\
     sumAndAverage_float64 right /\
     ~sumAndAverage_binary64IsNaN left /\
     ~sumAndAverage_binary64IsNaN right /\
     (left = right \/
      (sumAndAverage_binary64IsZero left /\
       sumAndAverage_binary64IsZero right))`;;

let sumAndAverage_resultBEq = new_definition
  `sumAndAverage_resultBEq
      (left:int#num) (right:int#num) <=>
     FST left = FST right /\
     sumAndAverage_floatBEq (SND left) (SND right)`;;

let sumAndAverage_sumTo =
  new_recursive_definition num_RECURSION
    `(sumAndAverage_sumTo 0 = 0) /\
     (!n:num.
        sumAndAverage_sumTo (SUC n) =
        sumAndAverage_sumTo n + SUC n)`;;

let sumAndAverage_precond = new_definition
  `sumAndAverage_precond (n:num) <=>
     n > 0 /\ n < 2 EXP 53`;;

let sumAndAverage = new_definition
  `sumAndAverage (n:num) =
     if n <= 0 then
       ((&0:int),0)
     else
       let sum = sumAndAverage_sumTo n in
       ((&sum:int),
        sumAndAverage_floatDiv
          (sumAndAverage_floatOfNum sum)
          (sumAndAverage_floatOfNum n))`;;

let sumAndAverage_postcond = new_definition
  `sumAndAverage_postcond
      (n:num) (result:int#num) <=>
     (n = 0 ==>
        sumAndAverage_resultBEq result ((&0:int),0)) /\
     (n > 0 ==>
        FST result = (&(n * (n + 1) DIV 2):int) /\
        sumAndAverage_floatBEq
          (SND result)
          (sumAndAverage_floatDiv
            (sumAndAverage_floatOfNum
              (n * (n + 1) DIV 2))
            (sumAndAverage_floatOfNum n)))`;;

let sumAndAverage_spec_satisfied =
  `!n:num.
     sumAndAverage_precond n
     ==> sumAndAverage_postcond n (sumAndAverage n)`;;
