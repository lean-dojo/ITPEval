(*
  Statement-only formalization of VERINA corpus artifact verina_basic_63
  (verina__hol-light__verina_basic_63), catalog title "has_close_elements":
  an executable nested scan decides whether two finite IEEE-754 binary64 list
  elements differ by less than a nonnegative threshold, with its precondition,
  pairwise postcondition, and correctness proposition. This file contains no
  proof.
*)

let verina63_float_INDUCT,verina63_float_RECURSION = define_type
  "verina63_float =
     V63Finite real | V63PosInf | V63NegInf | V63NaN";;

let verina63_binary64Magnitude = new_definition
  `verina63_binary64Magnitude (q:num) (f:num) =
     if q = 0 then
       (&f:real) / &(2 EXP 1074)
     else if q <= 1075 then
       (&(2 EXP 52 + f):real) / &(2 EXP (1075 - q))
     else
       (&(2 EXP 52 + f):real) * &(2 EXP (q - 1075))`;;

let verina63_binary64Finite = new_definition
  `verina63_binary64Finite (x:real) <=>
     ?negative:bool. ?q:num. ?f:num.
       q < 2047 /\
       f < 2 EXP 52 /\
       x =
         if negative then
           --(verina63_binary64Magnitude q f)
         else
           verina63_binary64Magnitude q f`;;

let verina63_binary64Even = new_definition
  `verina63_binary64Even (x:real) <=>
     ?negative:bool. ?q:num. ?f:num.
       q < 2047 /\
       f < 2 EXP 52 /\
       f MOD 2 = 0 /\
       x =
         if negative then
           --(verina63_binary64Magnitude q f)
         else
           verina63_binary64Magnitude q f`;;

let verina63_overflowThreshold = new_definition
  `verina63_overflowThreshold =
     (&(2 EXP 1024):real) - &(2 EXP 970)`;;

let verina63_roundBinary64 = new_definition
  `verina63_roundBinary64 (x:real) =
     if verina63_overflowThreshold <= x then
       V63PosInf
     else if x <= --verina63_overflowThreshold then
       V63NegInf
     else
       V63Finite
         (@y:real.
            verina63_binary64Finite y /\
            (!z:real.
               verina63_binary64Finite z
               ==> abs (x - y) <= abs (x - z)) /\
            (!z:real.
               verina63_binary64Finite z /\
               abs (x - y) = abs (x - z) /\
               verina63_binary64Even z
               ==> verina63_binary64Even y))`;;

let verina63_floatValue =
  new_recursive_definition verina63_float_RECURSION
    `(!x:real. verina63_floatValue (V63Finite x) = x) /\
     (verina63_floatValue V63PosInf = (&0:real)) /\
     (verina63_floatValue V63NegInf = (&0:real)) /\
     (verina63_floatValue V63NaN = (&0:real))`;;

let verina63_floatIsNaN = new_definition
  `verina63_floatIsNaN (x:verina63_float) <=> x = V63NaN`;;

let verina63_floatIsInf = new_definition
  `verina63_floatIsInf (x:verina63_float) <=>
     x = V63PosInf \/ x = V63NegInf`;;

let verina63_floatWellformed = new_definition
  `verina63_floatWellformed (x:verina63_float) <=>
     (?r:real. x = V63Finite r /\ verina63_binary64Finite r) \/
     x = V63PosInf \/
     x = V63NegInf \/
     x = V63NaN`;;

let verina63_floatLe = new_definition
  `verina63_floatLe (x:verina63_float) (y:verina63_float) <=>
     if verina63_floatIsNaN x \/ verina63_floatIsNaN y then
       F
     else if x = V63NegInf then
       T
     else if y = V63PosInf then
       T
     else if x = V63PosInf then
       x = y
     else if y = V63NegInf then
       x = y
     else
       verina63_floatValue x <= verina63_floatValue y`;;

let verina63_floatLt = new_definition
  `verina63_floatLt (x:verina63_float) (y:verina63_float) <=>
     verina63_floatLe x y /\ ~(verina63_floatLe y x)`;;

let verina63_floatSub = new_definition
  `verina63_floatSub (x:verina63_float) (y:verina63_float) =
     if verina63_floatIsNaN x \/ verina63_floatIsNaN y then
       V63NaN
     else if x = V63PosInf then
       if y = V63PosInf then V63NaN else V63PosInf
     else if x = V63NegInf then
       if y = V63NegInf then V63NaN else V63NegInf
     else if y = V63PosInf then
       V63NegInf
     else if y = V63NegInf then
       V63PosInf
     else
       verina63_roundBinary64
         (verina63_floatValue x - verina63_floatValue y)`;;

let absDiff = new_definition
  `absDiff (a:verina63_float) (b:verina63_float) =
     let d = verina63_floatSub a b in
     if verina63_floatLt d (V63Finite (&0:real)) then
       verina63_floatSub b a
     else
       d`;;

let has_close_elements_precond = new_definition
  `has_close_elements_precond
      (numbers:verina63_float list) (threshold:verina63_float) <=>
     verina63_floatWellformed threshold /\
     ALL verina63_floatWellformed numbers /\
     verina63_floatLe (V63Finite (&0:real)) threshold /\
     ~(verina63_floatIsNaN threshold) /\
     ALL
       (\x:verina63_float.
          ~(verina63_floatIsNaN x) /\ ~(verina63_floatIsInf x))
       numbers`;;

let has_close_elements_getDefault = new_definition
  `has_close_elements_getDefault
      (numbers:verina63_float list) (index:num) =
     if index < LENGTH numbers then
       EL index numbers
     else
       V63Finite (&0:real)`;;

let has_close_elements_inner =
  new_recursive_definition num_RECURSION
    `(!numbers:verina63_float list.
      !threshold:verina63_float.
      !idx idx2:num.
        has_close_elements_inner 0 numbers threshold idx idx2 = F) /\
     (!fuel:num.
      !numbers:verina63_float list.
      !threshold:verina63_float.
      !idx idx2:num.
        has_close_elements_inner (SUC fuel) numbers threshold idx idx2 =
        let a = has_close_elements_getDefault numbers idx2 in
        let b = has_close_elements_getDefault numbers idx in
        let d = absDiff a b in
        if verina63_floatLt d threshold then
          T
        else
          has_close_elements_inner
            fuel numbers threshold idx (SUC idx2))`;;

let has_close_elements_outer =
  new_recursive_definition num_RECURSION
    `(!numbers:verina63_float list.
      !threshold:verina63_float.
      !idx:num.
        has_close_elements_outer 0 numbers threshold idx = F) /\
     (!fuel:num.
      !numbers:verina63_float list.
      !threshold:verina63_float.
      !idx:num.
        has_close_elements_outer (SUC fuel) numbers threshold idx =
        if has_close_elements_inner idx numbers threshold idx 0 then
          T
        else
          has_close_elements_outer
            fuel numbers threshold (SUC idx))`;;

let has_close_elements = new_definition
  `has_close_elements
      (numbers:verina63_float list) (threshold:verina63_float) =
     has_close_elements_outer
       (LENGTH numbers) numbers threshold 0`;;

let has_close_elements_postcond = new_definition
  `has_close_elements_postcond
      (numbers:verina63_float list)
      (threshold:verina63_float)
      (result:bool) <=>
     ~result <=>
     PAIRWISE
       (\a b:verina63_float.
          verina63_floatLe threshold (absDiff a b))
       numbers`;;

let has_close_elements_spec_satisfied =
  `!numbers:verina63_float list. !threshold:verina63_float.
     has_close_elements_precond numbers threshold
     ==> has_close_elements_postcond
           numbers threshold
           (has_close_elements numbers threshold)`;;
