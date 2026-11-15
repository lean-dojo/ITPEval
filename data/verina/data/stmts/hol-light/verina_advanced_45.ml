(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_45,
  catalog title "maxSubarraySum": an executable Kadane scan computes the
  maximum sum of a nonempty contiguous subarray of an integer list, returning
  zero on the empty list, with an exhaustive maximality postcondition. This
  file contains no proof.
*)

let maxSubarraySum_precond = new_definition
  `maxSubarraySum_precond (xs:int list) <=> T`;;

let maxSubarraySum_max = new_definition
  `maxSubarraySum_max (a:int) (b:int) =
     if a <= b then b else a`;;

let maxSubarraySum_helper =
  new_recursive_definition list_RECURSION
    `(!curMax:int. !globalMax:int.
        maxSubarraySum_helper
          ([]:int list) curMax globalMax =
        globalMax) /\
     (!x:int. !rest:int list. !curMax:int. !globalMax:int.
        maxSubarraySum_helper
          (CONS x rest) curMax globalMax =
        let newCurMax =
          maxSubarraySum_max x (curMax + x) in
        let newGlobal =
          maxSubarraySum_max globalMax newCurMax in
        maxSubarraySum_helper
          rest newCurMax newGlobal)`;;

let maxSubarraySum = new_definition
  `maxSubarraySum (xs:int list) =
     if xs = [] then (&0:int)
     else
       maxSubarraySum_helper
         (TL xs) (HD xs) (HD xs)`;;

let maxSubarraySum_range =
  new_recursive_definition num_RECURSION
    `(maxSubarraySum_range 0 = []) /\
     (!n:num.
        maxSubarraySum_range (SUC n) =
        APPEND
          (maxSubarraySum_range n)
          (CONS n []))`;;

let maxSubarraySum_positiveLengths = new_definition
  `maxSubarraySum_positiveLengths (n:num) =
     MAP SUC (maxSubarraySum_range n)`;;

let maxSubarraySum_drop =
  new_recursive_definition num_RECURSION
    `(!xs:int list.
        maxSubarraySum_drop 0 xs = xs) /\
     (!n:num. !xs:int list.
        maxSubarraySum_drop (SUC n) xs =
        if xs = [] then []
        else maxSubarraySum_drop n (TL xs))`;;

let maxSubarraySum_take =
  new_recursive_definition num_RECURSION
    `(!xs:int list.
        maxSubarraySum_take 0 xs = []) /\
     (!n:num. !xs:int list.
        maxSubarraySum_take (SUC n) xs =
        if xs = [] then []
        else
          CONS (HD xs)
            (maxSubarraySum_take n (TL xs)))`;;

let maxSubarraySum_sum =
  new_recursive_definition list_RECURSION
    `(maxSubarraySum_sum ([]:int list) = (&0:int)) /\
     (!x:int. !xs:int list.
        maxSubarraySum_sum (CONS x xs) =
        x + maxSubarraySum_sum xs)`;;

let maxSubarraySum_sumsAt = new_definition
  `maxSubarraySum_sumsAt
      (xs:int list) (start:num) =
     MAP
       (\len:num.
          maxSubarraySum_sum
            (maxSubarraySum_take len
              (maxSubarraySum_drop start xs)))
       (maxSubarraySum_positiveLengths
         (LENGTH xs - start))`;;

let maxSubarraySum_allSumsFrom =
  new_recursive_definition list_RECURSION
    `(!xs:int list.
        maxSubarraySum_allSumsFrom
          xs ([]:num list) = []) /\
     (!start:num. !starts:num list. !xs:int list.
        maxSubarraySum_allSumsFrom
          xs (CONS start starts) =
        APPEND
          (maxSubarraySum_sumsAt xs start)
          (maxSubarraySum_allSumsFrom xs starts))`;;

let maxSubarraySum_subarraySums = new_definition
  `maxSubarraySum_subarraySums (xs:int list) =
     maxSubarraySum_allSumsFrom
       xs
       (maxSubarraySum_range (LENGTH xs + 1))`;;

let maxSubarraySum_postcond = new_definition
  `maxSubarraySum_postcond
      (xs:int list) (result:int) <=>
     let subarraySums =
       maxSubarraySum_subarraySums xs in
     if xs = [] then result = (&0:int)
     else
       MEM result subarraySums /\
       ALL (\s:int. s <= result) subarraySums`;;

let maxSubarraySum_spec_satisfied =
  `!xs:int list.
     maxSubarraySum_precond xs
     ==> maxSubarraySum_postcond
           xs (maxSubarraySum xs)`;;
