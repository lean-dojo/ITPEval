(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_30,
  catalog title "longestIncreasingStreak": an executable recursive scan
  computes the maximum length of a strictly increasing contiguous streak in
  an integer list, with its boundary and maximality postcondition. This file
  contains no proof.
*)

let longestIncreasingStreak_precond = new_definition
  `longestIncreasingStreak_precond (nums:int list) <=> T`;;

let longestIncreasingStreak_optionValue = new_definition
  `longestIncreasingStreak_optionValue (value:int option) =
     @x:int. value = SOME x`;;

let longestIncreasingStreak_aux =
  new_recursive_definition list_RECURSION
    `(!prev:int option. !currLen:num. !maxLen:num.
        longestIncreasingStreak_aux
          ([]:int list) prev currLen maxLen =
        if currLen >= maxLen then currLen else maxLen) /\
     (!x:int. !xs:int list. !prev:int option.
      !currLen:num. !maxLen:num.
        longestIncreasingStreak_aux
          (CONS x xs) prev currLen maxLen =
        if prev = NONE then
          longestIncreasingStreak_aux
            xs (SOME x) 1
            (if 1 >= maxLen then 1 else maxLen)
        else
          let p =
            longestIncreasingStreak_optionValue prev in
          if x > p then
            let nextLen = currLen + 1 in
            longestIncreasingStreak_aux
              xs (SOME x) nextLen
              (if nextLen >= maxLen
               then nextLen
               else maxLen)
          else
            longestIncreasingStreak_aux
              xs (SOME x) 1
              (if currLen >= maxLen
               then currLen
               else maxLen))`;;

let longestIncreasingStreak = new_definition
  `longestIncreasingStreak (nums:int list) =
     longestIncreasingStreak_aux nums NONE 0 0`;;

let longestIncreasingStreak_range =
  new_recursive_definition num_RECURSION
    `(longestIncreasingStreak_range 0 = []) /\
     (!n:num.
        longestIncreasingStreak_range (SUC n) =
        APPEND
          (longestIncreasingStreak_range n)
          (CONS n []))`;;

let longestIncreasingStreak_get =
  new_recursive_definition num_RECURSION
    `(!nums:int list.
        longestIncreasingStreak_get 0 nums =
        if nums = [] then (&0:int) else HD nums) /\
     (!index:num. !nums:int list.
        longestIncreasingStreak_get (SUC index) nums =
        if nums = []
        then (&0:int)
        else longestIncreasingStreak_get index (TL nums))`;;

let longestIncreasingStreak_postcond = new_definition
  `longestIncreasingStreak_postcond
      (nums:int list) (result:num) <=>
     (nums = [] ==> result = 0) /\
     (result > 0 ==>
       EX
         (\start:num.
            start + result <= LENGTH nums /\
            ALL
              (\i:num.
                 longestIncreasingStreak_get
                   (start + i) nums <
                 longestIncreasingStreak_get
                   (start + i + 1) nums)
              (longestIncreasingStreak_range
                (result - 1)) /\
            (start = 0 \/
             longestIncreasingStreak_get
               (start - 1) nums >=
             longestIncreasingStreak_get start nums) /\
            (start + result = LENGTH nums \/
             longestIncreasingStreak_get
               (start + result - 1) nums >=
             longestIncreasingStreak_get
               (start + result) nums))
         (longestIncreasingStreak_range
           (LENGTH nums - result + 1))) /\
     ALL
       (\start:num.
          EX
            (\i:num.
               start + i + 1 >= LENGTH nums \/
               longestIncreasingStreak_get
                 (start + i) nums >=
               longestIncreasingStreak_get
                 (start + i + 1) nums)
            (longestIncreasingStreak_range result))
       (longestIncreasingStreak_range
         (LENGTH nums - result))`;;

let longestIncreasingStreak_spec_satisfied =
  `!nums:int list.
     longestIncreasingStreak_precond nums
     ==> longestIncreasingStreak_postcond
           nums (longestIncreasingStreak nums)`;;
