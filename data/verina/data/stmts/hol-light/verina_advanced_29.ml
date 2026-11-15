(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_29,
  catalog title "longestGoodSubarray": an executable sliding-window frequency
  scan returns the maximum length of a contiguous natural-number subarray in
  which every value occurs at most k times. This file contains no proof.
*)

let longestGoodSubarray_precond = new_definition
  `longestGoodSubarray_precond (nums:num list) (k:num) <=>
     k > 0`;;

let longestGoodSubarray_mapGet =
  new_recursive_definition list_RECURSION
    `(longestGoodSubarray_mapGet
        (key:num) ([]:(num#num)list) = 0) /\
     (!entry:num#num. !rest:(num#num)list. !key:num.
        longestGoodSubarray_mapGet key (CONS entry rest) =
        if FST entry = key
        then SND entry
        else longestGoodSubarray_mapGet key rest)`;;

let longestGoodSubarray_mapInsert =
  new_recursive_definition list_RECURSION
    `(longestGoodSubarray_mapInsert
        (key:num) (value:num) ([]:(num#num)list) =
        CONS (key,value) []) /\
     (!entry:num#num. !rest:(num#num)list.
      !key:num. !value:num.
        longestGoodSubarray_mapInsert
          key value (CONS entry rest) =
        if FST entry = key
        then CONS (key,value) rest
        else
          CONS entry
            (longestGoodSubarray_mapInsert
              key value rest))`;;

let longestGoodSubarray_mapErase =
  new_recursive_definition list_RECURSION
    `(longestGoodSubarray_mapErase
        (key:num) ([]:(num#num)list) = []) /\
     (!entry:num#num. !rest:(num#num)list. !key:num.
        longestGoodSubarray_mapErase key (CONS entry rest) =
        if FST entry = key
        then rest
        else
          CONS entry
            (longestGoodSubarray_mapErase key rest))`;;

let longestGoodSubarray_hasExcess =
  new_recursive_definition list_RECURSION
    `(longestGoodSubarray_hasExcess
        (k:num) ([]:(num#num)list) <=> F) /\
     (!entry:num#num. !rest:(num#num)list. !k:num.
        longestGoodSubarray_hasExcess
          k (CONS entry rest) <=>
        SND entry > k \/
        longestGoodSubarray_hasExcess k rest)`;;

let longestGoodSubarray_get =
  new_recursive_definition num_RECURSION
    `(!nums:num list.
        longestGoodSubarray_get 0 nums =
        if nums = [] then 0 else HD nums) /\
     (!index:num. !nums:num list.
        longestGoodSubarray_get (SUC index) nums =
        if nums = []
        then 0
        else longestGoodSubarray_get index (TL nums))`;;

let longestGoodSubarray_shrink =
  new_recursive_definition num_RECURSION
    `(!nums:num list. !k:num. !left:num.
      !freq:(num#num)list.
        longestGoodSubarray_shrink
          0 nums k left freq = (left,freq)) /\
     (!fuel:num. !nums:num list. !k:num. !left:num.
      !freq:(num#num)list.
        longestGoodSubarray_shrink
          (SUC fuel) nums k left freq =
        if longestGoodSubarray_hasExcess k freq then
          let lnum =
            longestGoodSubarray_get left nums in
          let lcount =
            longestGoodSubarray_mapGet lnum freq in
          let nextFreq =
            if lcount = 1
            then longestGoodSubarray_mapErase lnum freq
            else
              longestGoodSubarray_mapInsert
                lnum (lcount - 1) freq in
          longestGoodSubarray_shrink
            fuel nums k (SUC left) nextFreq
        else (left,freq))`;;

let longestGoodSubarray_outer =
  new_recursive_definition num_RECURSION
    `(!nums:num list. !k:num. !right:num. !left:num.
      !maxLen:num. !freq:(num#num)list.
        longestGoodSubarray_outer
          0 nums k right left maxLen freq = maxLen) /\
     (!fuel:num. !nums:num list. !k:num.
      !right:num. !left:num. !maxLen:num.
      !freq:(num#num)list.
        longestGoodSubarray_outer
          (SUC fuel) nums k right left maxLen freq =
        let num =
          longestGoodSubarray_get right nums in
        let count =
          longestGoodSubarray_mapGet num freq in
        let grownFreq =
          longestGoodSubarray_mapInsert
            num (count + 1) freq in
        let shrunk =
          longestGoodSubarray_shrink
            (LENGTH nums) nums k left grownFreq in
        let nextLeft = FST shrunk in
        let nextFreq = SND shrunk in
        let windowLen = right - nextLeft + 1 in
        let nextMax =
          if maxLen >= windowLen
          then maxLen
          else windowLen in
        longestGoodSubarray_outer
          fuel nums k (SUC right) nextLeft
          nextMax nextFreq)`;;

let longestGoodSubarray = new_definition
  `longestGoodSubarray (nums:num list) (k:num) =
     longestGoodSubarray_outer
       (LENGTH nums) nums k 0 0 0 []`;;

let longestGoodSubarray_range =
  new_recursive_definition num_RECURSION
    `(longestGoodSubarray_range 0 = []) /\
     (!n:num.
        longestGoodSubarray_range (SUC n) =
        APPEND
          (longestGoodSubarray_range n)
          (CONS n []))`;;

let longestGoodSubarray_drop =
  new_recursive_definition num_RECURSION
    `(!nums:num list.
        longestGoodSubarray_drop 0 nums = nums) /\
     (!n:num. !nums:num list.
        longestGoodSubarray_drop (SUC n) nums =
        if nums = []
        then []
        else longestGoodSubarray_drop n (TL nums))`;;

let longestGoodSubarray_take =
  new_recursive_definition num_RECURSION
    `(!nums:num list.
        longestGoodSubarray_take 0 nums = []) /\
     (!n:num. !nums:num list.
        longestGoodSubarray_take (SUC n) nums =
        if nums = []
        then []
        else
          CONS (HD nums)
            (longestGoodSubarray_take n (TL nums)))`;;

let longestGoodSubarray_slicesAt = new_definition
  `longestGoodSubarray_slicesAt
      (nums:num list) (start:num) =
     MAP
       (\len:num.
          longestGoodSubarray_take len
            (longestGoodSubarray_drop start nums))
       (longestGoodSubarray_range
         (LENGTH nums - start + 1))`;;

let longestGoodSubarray_allSlicesFrom =
  new_recursive_definition list_RECURSION
    `(!nums:num list.
        longestGoodSubarray_allSlicesFrom nums [] = []) /\
     (!start:num. !starts:num list. !nums:num list.
        longestGoodSubarray_allSlicesFrom
          nums (CONS start starts) =
        APPEND
          (longestGoodSubarray_slicesAt nums start)
          (longestGoodSubarray_allSlicesFrom
            nums starts))`;;

let longestGoodSubarray_allSlices = new_definition
  `longestGoodSubarray_allSlices (nums:num list) =
     longestGoodSubarray_allSlicesFrom nums
       (longestGoodSubarray_range
         (LENGTH nums + 1))`;;

let longestGoodSubarray_count = new_definition
  `longestGoodSubarray_count
      (x:num) (arr:num list) =
     LENGTH (FILTER (\y:num. y = x) arr)`;;

let longestGoodSubarray_frequencies = new_definition
  `longestGoodSubarray_frequencies (arr:num list) =
     MAP
       (\x:num. longestGoodSubarray_count x arr)
       arr`;;

let longestGoodSubarray_postcond = new_definition
  `longestGoodSubarray_postcond
      (nums:num list) (k:num) (result:num) <=>
     let subArrays =
       longestGoodSubarray_allSlices nums in
     let subArrayFreqs =
       MAP longestGoodSubarray_frequencies subArrays in
     let validSubArrays =
       FILTER
         (\arr:num list.
            ALL (\count:num. count <= k) arr)
         subArrayFreqs in
     (nums = [] /\ result = 0) \/
     (~(nums = []) /\
       EX
         (\arr:num list. LENGTH arr = result)
         validSubArrays /\
       ALL
         (\arr:num list. LENGTH arr <= result)
         validSubArrays)`;;

let longestGoodSubarray_spec_satisfied =
  `!nums:num list. !k:num.
     longestGoodSubarray_precond nums k
     ==> longestGoodSubarray_postcond
           nums k (longestGoodSubarray nums k)`;;
