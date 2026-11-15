(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_44,
  catalog title "maxSubarraySumDivisibleByK": a prefix-sum enumeration computes
  the maximum sum of a contiguous integer subarray whose positive length is
  divisible by k, with its positive-k precondition, exhaustive postcondition,
  and unconditional correctness proposition. This file contains no proof.
*)

let maxSubarraySumDivisibleByK_precond = new_definition
  `maxSubarraySumDivisibleByK_precond
      (arr:int list) (k:int) <=>
     k > &0`;;

let maxSubarraySumDivisibleByK_range =
  new_recursive_definition num_RECURSION
    `(maxSubarraySumDivisibleByK_range 0 = []) /\
     (!n:num.
        maxSubarraySumDivisibleByK_range (SUC n) =
        APPEND
          (maxSubarraySumDivisibleByK_range n)
          (CONS n []))`;;

let maxSubarraySumDivisibleByK_get =
  new_recursive_definition num_RECURSION
    `(!xs:int list.
        maxSubarraySumDivisibleByK_get 0 xs =
        if xs = [] then (&0:int) else HD xs) /\
     (!index:num. !xs:int list.
        maxSubarraySumDivisibleByK_get (SUC index) xs =
        if xs = [] then (&0:int)
        else maxSubarraySumDivisibleByK_get index (TL xs))`;;

let maxSubarraySumDivisibleByK_prefixBuild =
  new_recursive_definition list_RECURSION
    `(!current:int. !acc:int list.
        maxSubarraySumDivisibleByK_prefixBuild
          ([]:int list) current acc = acc) /\
     (!x:int. !xs:int list. !current:int. !acc:int list.
        maxSubarraySumDivisibleByK_prefixBuild
          (CONS x xs) current acc =
        let next = current + x in
        maxSubarraySumDivisibleByK_prefixBuild
          xs next (APPEND acc (CONS next [])))`;;

let maxSubarraySumDivisibleByK_prefixSums = new_definition
  `maxSubarraySumDivisibleByK_prefixSums (arr:int list) =
     maxSubarraySumDivisibleByK_prefixBuild
       arr (&0:int) (CONS (&0:int) [])`;;

let maxSubarraySumDivisibleByK_optionValue =
  new_recursive_definition option_RECURSION
    `(maxSubarraySumDivisibleByK_optionValue
        (NONE:int option) = (&0:int)) /\
     (!x:int.
        maxSubarraySumDivisibleByK_optionValue (SOME x) = x)`;;

let maxSubarraySumDivisibleByK_updateBest = new_definition
  `maxSubarraySumDivisibleByK_updateBest
      (best:int option) (candidate:int) =
     if best = NONE then SOME candidate
     else
       let previous =
         maxSubarraySumDivisibleByK_optionValue best in
       SOME
         (if previous <= candidate
          then candidate
          else previous)`;;

let maxSubarraySumDivisibleByK_scanStarts =
  new_recursive_definition list_RECURSION
    `(!len:num. !prefixSums:int list. !best:int option.
        maxSubarraySumDivisibleByK_scanStarts
          ([]:num list) len prefixSums best = best) /\
     (!start:num. !starts:num list. !len:num.
      !prefixSums:int list. !best:int option.
        maxSubarraySumDivisibleByK_scanStarts
          (CONS start starts) len prefixSums best =
        let subarraySum =
          maxSubarraySumDivisibleByK_get
            (start + len) prefixSums -
          maxSubarraySumDivisibleByK_get
            start prefixSums in
        maxSubarraySumDivisibleByK_scanStarts
          starts len prefixSums
          (maxSubarraySumDivisibleByK_updateBest
            best subarraySum))`;;

let maxSubarraySumDivisibleByK_lengthDivisible = new_definition
  `maxSubarraySumDivisibleByK_lengthDivisible
      (len:num) (k:int) <=>
     ?q:int. (&len:int) = k * q`;;

let maxSubarraySumDivisibleByK_scanLengths =
  new_recursive_definition list_RECURSION
    `(!n:num. !k:int. !prefixSums:int list. !best:int option.
        maxSubarraySumDivisibleByK_scanLengths
          ([]:num list) n k prefixSums best = best) /\
     (!len:num. !lens:num list. !n:num. !k:int.
      !prefixSums:int list. !best:int option.
        maxSubarraySumDivisibleByK_scanLengths
          (CONS len lens) n k prefixSums best =
        let nextBest =
          if
            maxSubarraySumDivisibleByK_lengthDivisible len k /\
            len > 0
          then
            maxSubarraySumDivisibleByK_scanStarts
              (maxSubarraySumDivisibleByK_range
                (n - len + 1))
              len prefixSums best
          else best in
        maxSubarraySumDivisibleByK_scanLengths
          lens n k prefixSums nextBest)`;;

let maxSubarraySumDivisibleByK = new_definition
  `maxSubarraySumDivisibleByK (arr:int list) (k:int) =
     let n = LENGTH arr in
     if n = 0 \/ k = &0 then (&0:int)
     else
       let prefixSums =
         maxSubarraySumDivisibleByK_prefixSums arr in
       let result =
         maxSubarraySumDivisibleByK_scanLengths
           (maxSubarraySumDivisibleByK_range (n + 1))
           n k prefixSums (NONE:int option) in
       if result = NONE then (&0:int)
       else maxSubarraySumDivisibleByK_optionValue result`;;

let maxSubarraySumDivisibleByK_drop =
  new_recursive_definition num_RECURSION
    `(!xs:int list.
        maxSubarraySumDivisibleByK_drop 0 xs = xs) /\
     (!n:num. !xs:int list.
        maxSubarraySumDivisibleByK_drop (SUC n) xs =
        if xs = [] then []
        else maxSubarraySumDivisibleByK_drop n (TL xs))`;;

let maxSubarraySumDivisibleByK_take =
  new_recursive_definition num_RECURSION
    `(!xs:int list.
        maxSubarraySumDivisibleByK_take 0 xs = []) /\
     (!n:num. !xs:int list.
        maxSubarraySumDivisibleByK_take (SUC n) xs =
        if xs = [] then []
        else
          CONS (HD xs)
            (maxSubarraySumDivisibleByK_take n (TL xs)))`;;

let maxSubarraySumDivisibleByK_slicesAt = new_definition
  `maxSubarraySumDivisibleByK_slicesAt
      (arr:int list) (start:num) =
     MAP
       (\len:num.
          maxSubarraySumDivisibleByK_take len
            (maxSubarraySumDivisibleByK_drop start arr))
       (maxSubarraySumDivisibleByK_range
         (LENGTH arr - start + 1))`;;

let maxSubarraySumDivisibleByK_allSlicesFrom =
  new_recursive_definition list_RECURSION
    `(!arr:int list.
        maxSubarraySumDivisibleByK_allSlicesFrom
          arr ([]:num list) = []) /\
     (!start:num. !starts:num list. !arr:int list.
        maxSubarraySumDivisibleByK_allSlicesFrom
          arr (CONS start starts) =
        APPEND
          (maxSubarraySumDivisibleByK_slicesAt arr start)
          (maxSubarraySumDivisibleByK_allSlicesFrom
            arr starts))`;;

let maxSubarraySumDivisibleByK_allSlices = new_definition
  `maxSubarraySumDivisibleByK_allSlices (arr:int list) =
     maxSubarraySumDivisibleByK_allSlicesFrom
       arr
       (maxSubarraySumDivisibleByK_range (LENGTH arr))`;;

let maxSubarraySumDivisibleByK_validSlice = new_definition
  `maxSubarraySumDivisibleByK_validSlice
      (k:int) (subarray:int list) <=>
     LENGTH subarray > 0 /\
     k > &0 /\
     (?q:int. (&(LENGTH subarray):int) = k * q)`;;

let maxSubarraySumDivisibleByK_sum =
  new_recursive_definition list_RECURSION
    `(maxSubarraySumDivisibleByK_sum ([]:int list) = (&0:int)) /\
     (!x:int. !xs:int list.
        maxSubarraySumDivisibleByK_sum (CONS x xs) =
        x + maxSubarraySumDivisibleByK_sum xs)`;;

let maxSubarraySumDivisibleByK_postcond = new_definition
  `maxSubarraySumDivisibleByK_postcond
      (arr:int list) (k:int) (result:int) <=>
     let subarrays =
       maxSubarraySumDivisibleByK_allSlices arr in
     let divisibleSubarrays =
       FILTER
         (maxSubarraySumDivisibleByK_validSlice k)
         subarrays in
     let subarraySums =
       MAP maxSubarraySumDivisibleByK_sum
         divisibleSubarrays in
     (LENGTH subarraySums = 0 ==> result = &0) /\
     (LENGTH subarraySums > 0
      ==> MEM result subarraySums /\
          ALL (\s:int. s <= result) subarraySums)`;;

let maxSubarraySumDivisibleByK_spec_satisfied =
  `!arr:int list. !k:int.
     maxSubarraySumDivisibleByK_postcond
       arr k (maxSubarraySumDivisibleByK arr k)`;;
