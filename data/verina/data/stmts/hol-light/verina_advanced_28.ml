(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_28,
  catalog title "longestConsecutive": an executable bounded set-membership
  scan returns the longest consecutive-integer streak length in a duplicate-
  free integer list, with its sorted-slice maximality postcondition. This file
  contains no proof.
*)

let longestConsecutive_nodup =
  new_recursive_definition list_RECURSION
    `(longestConsecutive_nodup ([]:int list) <=> T) /\
     (!x:int. !xs:int list.
        longestConsecutive_nodup (CONS x xs) <=>
        ~(MEM x xs) /\ longestConsecutive_nodup xs)`;;

let longestConsecutive_precond = new_definition
  `longestConsecutive_precond (nums:int list) <=>
     longestConsecutive_nodup nums`;;

let longestConsecutive_setFold =
  new_recursive_definition list_RECURSION
    `(!set:int list.
        longestConsecutive_setFold set [] = set) /\
     (!x:int. !xs:int list. !set:int list.
        longestConsecutive_setFold set (CONS x xs) =
        longestConsecutive_setFold
          (if MEM x set then set else CONS x set) xs)`;;

let longestConsecutive_buildSet = new_definition
  `longestConsecutive_buildSet (nums:int list) =
     longestConsecutive_setFold [] nums`;;

let longestConsecutive_scan =
  new_recursive_definition num_RECURSION
    `(!set:int list. !curr:int. !length:num.
        longestConsecutive_scan 0 set curr length = length) /\
     (!fuel:num. !set:int list. !curr:int. !length:num.
        longestConsecutive_scan (SUC fuel) set curr length =
        if MEM (curr + &1) set
        then
          longestConsecutive_scan fuel set
            (curr + &1) (length + 1)
        else length)`;;

let longestConsecutive_outer =
  new_recursive_definition list_RECURSION
    `(!set:int list. !bound:num. !maxLen:num.
        longestConsecutive_outer
          ([]:int list) set bound maxLen = maxLen) /\
     (!x:int. !xs:int list. !set:int list.
      !bound:num. !maxLen:num.
        longestConsecutive_outer
          (CONS x xs) set bound maxLen =
        let nextMax =
          if ~(MEM (x - &1) set) then
            let streak =
              longestConsecutive_scan bound set x 1 in
            if maxLen >= streak then maxLen else streak
          else maxLen in
        longestConsecutive_outer
          xs set bound nextMax)`;;

let longestConsecutive = new_definition
  `longestConsecutive (nums:int list) =
     let set = longestConsecutive_buildSet nums in
     longestConsecutive_outer
       nums set (LENGTH nums) 0`;;

let longestConsecutive_sortInsert =
  new_recursive_definition list_RECURSION
    `(longestConsecutive_sortInsert
        (x:int) [] = CONS x []) /\
     (!y:int. !ys:int list. !x:int.
        longestConsecutive_sortInsert x (CONS y ys) =
        if x <= y
        then CONS x (CONS y ys)
        else
          CONS y
            (longestConsecutive_sortInsert x ys))`;;

let longestConsecutive_sort =
  new_recursive_definition list_RECURSION
    `(longestConsecutive_sort ([]:int list) = []) /\
     (!x:int. !xs:int list.
        longestConsecutive_sort (CONS x xs) =
        longestConsecutive_sortInsert x
          (longestConsecutive_sort xs))`;;

let longestConsecutive_range =
  new_recursive_definition num_RECURSION
    `(longestConsecutive_range 0 = []) /\
     (!n:num.
        longestConsecutive_range (SUC n) =
        APPEND (longestConsecutive_range n)
          (CONS n []))`;;

let longestConsecutive_drop =
  new_recursive_definition num_RECURSION
    `(!xs:int list.
        longestConsecutive_drop 0 xs = xs) /\
     (!n:num. !xs:int list.
        longestConsecutive_drop (SUC n) xs =
        if xs = [] then []
        else longestConsecutive_drop n (TL xs))`;;

let longestConsecutive_take =
  new_recursive_definition num_RECURSION
    `(!xs:int list.
        longestConsecutive_take 0 xs = []) /\
     (!n:num. !xs:int list.
        longestConsecutive_take (SUC n) xs =
        if xs = [] then []
        else
          CONS (HD xs)
            (longestConsecutive_take n (TL xs)))`;;

let longestConsecutive_extract = new_definition
  `longestConsecutive_extract
      (start:num) (stop:num) (xs:int list) =
     longestConsecutive_take (stop - start)
       (longestConsecutive_drop start xs)`;;

let longestConsecutive_slicesAt = new_definition
  `longestConsecutive_slicesAt
      (sorted_nums:int list) (n:num) (start:num) =
     MAP
       (\len:num.
          longestConsecutive_extract
            start (start + len) sorted_nums)
       (longestConsecutive_range (n - start + 1))`;;

let longestConsecutive_allSlicesFrom =
  new_recursive_definition list_RECURSION
    `(!sorted_nums:int list. !n:num.
        longestConsecutive_allSlicesFrom
          sorted_nums n [] = []) /\
     (!start:num. !starts:num list.
      !sorted_nums:int list. !n:num.
        longestConsecutive_allSlicesFrom
          sorted_nums n (CONS start starts) =
        APPEND
          (longestConsecutive_slicesAt
            sorted_nums n start)
          (longestConsecutive_allSlicesFrom
            sorted_nums n starts))`;;

let longestConsecutive_allSlices = new_definition
  `longestConsecutive_allSlices
      (sorted_nums:int list) (n:num) =
     longestConsecutive_allSlicesFrom
       sorted_nums n (longestConsecutive_range n)`;;

let longestConsecutive_isConsecutiveFrom =
  new_recursive_definition list_RECURSION
    `(!base:int. !index:num.
        longestConsecutive_isConsecutiveFrom
          base index [] <=> T) /\
     (!x:int. !xs:int list. !base:int. !index:num.
        longestConsecutive_isConsecutiveFrom
          base index (CONS x xs) <=>
        x = base + &index /\
        longestConsecutive_isConsecutiveFrom
          base (SUC index) xs)`;;

let isConsecutive = new_definition
  `isConsecutive (seq:int list) <=>
     seq = [] \/
     longestConsecutive_isConsecutiveFrom
       (HD seq) 0 seq`;;

let longestConsecutive_postcond = new_definition
  `longestConsecutive_postcond
      (nums:int list) (result:num) <=>
     let sorted_nums = longestConsecutive_sort nums in
     let consec_sublist_lens =
       MAP (\seq:int list. LENGTH seq)
         (FILTER isConsecutive
           (longestConsecutive_allSlices
             sorted_nums (LENGTH nums))) in
     (nums = [] ==> result = 0) /\
     (~(nums = []) ==>
       MEM result consec_sublist_lens /\
       ALL (\len:num. len <= result)
         consec_sublist_lens)`;;

let longestConsecutive_spec_satisfied =
  `!nums:int list.
     longestConsecutive_precond nums
     ==> longestConsecutive_postcond
           nums (longestConsecutive nums)`;;
