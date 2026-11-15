(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_46,
  catalog title "maxSubarraySum": an executable all-negative test and
  Kadane-style scan compute an integer result via Lean's natural-number
  conversion, with a postcondition asserting membership and maximality among
  all contiguous-subarray sums, including empty subarrays. This file contains
  no proof.
*)

let maxSubarraySum_precond = new_definition
  `maxSubarraySum_precond (numbers:int list) <=> T`;;

let maxSubarraySum_max = new_definition
  `maxSubarraySum_max (a:int) (b:int) =
     if a <= b then b else a`;;

let maxSubarraySum_isAllNegative =
  new_recursive_definition list_RECURSION
    `(maxSubarraySum_isAllNegative ([]:int list) <=> T) /\
     (!x:int. !xs:int list.
        maxSubarraySum_isAllNegative (CONS x xs) <=>
        if &0 <= x then F
        else maxSubarraySum_isAllNegative xs)`;;

let maxSubarraySum_findMaxProduct =
  new_recursive_definition list_RECURSION
    `(!currMax:int. !currSum:int.
        maxSubarraySum_findMaxProduct
          ([]:int list) currMax currSum =
        currMax) /\
     (!x:int. !xs:int list. !currMax:int. !currSum:int.
        maxSubarraySum_findMaxProduct
          (CONS x xs) currMax currSum =
        if xs = [] then
          maxSubarraySum_max currMax x
        else
          let y = HD xs in
          let newSum =
            maxSubarraySum_max y (currSum + y) in
          let newMax =
            maxSubarraySum_max currMax newSum in
          maxSubarraySum_findMaxProduct
            xs newMax newSum)`;;

let maxSubarraySum_intToNat = new_definition
  `maxSubarraySum_intToNat (z:int) =
     if z < &0 then 0 else num_of_int z`;;

let maxSubarraySum_handleList = new_definition
  `maxSubarraySum_handleList (numbers:int list) =
     if numbers = [] then 0
     else if maxSubarraySum_isAllNegative numbers then 0
     else
       let x = HD numbers in
       let initialMax =
         maxSubarraySum_max (&0:int) x in
       let startSum =
         maxSubarraySum_max (&0:int) x in
       let result =
         maxSubarraySum_findMaxProduct
           numbers initialMax startSum in
       maxSubarraySum_intToNat result`;;

let maxSubarraySum = new_definition
  `maxSubarraySum (numbers:int list) =
     (&(maxSubarraySum_handleList numbers):int)`;;

let maxSubarraySum_range =
  new_recursive_definition num_RECURSION
    `(maxSubarraySum_range 0 = []) /\
     (!n:num.
        maxSubarraySum_range (SUC n) =
        APPEND
          (maxSubarraySum_range n)
          (CONS n []))`;;

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
      (numbers:int list) (start:num) =
     MAP
       (\len:num.
          maxSubarraySum_sum
            (maxSubarraySum_take len
              (maxSubarraySum_drop start numbers)))
       (maxSubarraySum_range
         (LENGTH numbers - start + 1))`;;

let maxSubarraySum_allSumsFrom =
  new_recursive_definition list_RECURSION
    `(!numbers:int list.
        maxSubarraySum_allSumsFrom
          numbers ([]:num list) = []) /\
     (!start:num. !starts:num list. !numbers:int list.
        maxSubarraySum_allSumsFrom
          numbers (CONS start starts) =
        APPEND
          (maxSubarraySum_sumsAt numbers start)
          (maxSubarraySum_allSumsFrom numbers starts))`;;

let maxSubarraySum_subarraySums = new_definition
  `maxSubarraySum_subarraySums (numbers:int list) =
     maxSubarraySum_allSumsFrom
       numbers
       (maxSubarraySum_range (LENGTH numbers + 1))`;;

let maxSubarraySum_postcond = new_definition
  `maxSubarraySum_postcond
      (numbers:int list) (result:int) <=>
     let subArraySums =
       maxSubarraySum_subarraySums numbers in
     MEM result subArraySums /\
     ALL (\s:int. s <= result) subArraySums`;;

let maxSubarraySum_spec_satisfied =
  `!numbers:int list.
     maxSubarraySum_precond numbers
     ==> maxSubarraySum_postcond
           numbers (maxSubarraySum numbers)`;;
