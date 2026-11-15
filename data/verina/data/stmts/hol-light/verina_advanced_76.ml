(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_76,
  catalog title "topKFrequent": a deterministic frequency-counting program
  stably sorts distinct integers by descending occurrence count and returns
  the first k, together with its full correctness contract. This file contains
  no proof.
*)

let topKFrequent_distinctFold =
  new_recursive_definition list_RECURSION
    `(!seen:int list.
        topKFrequent_distinctFold ([]:int list) seen = seen) /\
     (!x:int. !xs:int list. !seen:int list.
        topKFrequent_distinctFold (CONS x xs) seen =
        topKFrequent_distinctFold xs
          (if MEM x seen then seen
           else APPEND seen (CONS x [])))`;;

let topKFrequent_distinct = new_definition
  `topKFrequent_distinct (nums:int list) =
     topKFrequent_distinctFold nums []`;;

let topKFrequent_precond = new_definition
  `topKFrequent_precond (nums:int list) (k:num) <=>
     k <= LENGTH (topKFrequent_distinct nums)`;;

let topKFrequent_hasKey =
  new_recursive_definition list_RECURSION
    `(!key:int.
        topKFrequent_hasKey ([]:(int#num)list) key <=> F) /\
     (!entry:int#num. !rest:(int#num)list. !key:int.
        topKFrequent_hasKey (CONS entry rest) key <=>
        FST entry = key \/ topKFrequent_hasKey rest key)`;;

let topKFrequent_increment =
  new_recursive_definition list_RECURSION
    `(!key:int.
        topKFrequent_increment ([]:(int#num)list) key = []) /\
     (!entry:int#num. !rest:(int#num)list. !key:int.
        topKFrequent_increment (CONS entry rest) key =
        if FST entry = key then
          CONS (FST entry,SND entry + 1)
            (topKFrequent_increment rest key)
        else
          CONS entry (topKFrequent_increment rest key))`;;

let topKFrequent_buildFreq =
  new_recursive_definition list_RECURSION
    `(!acc:(int#num)list.
        topKFrequent_buildFreq ([]:int list) acc = acc) /\
     (!x:int. !xs:int list. !acc:(int#num)list.
        topKFrequent_buildFreq (CONS x xs) acc =
        topKFrequent_buildFreq xs
          (if topKFrequent_hasKey acc x then
             topKFrequent_increment acc x
           else
             APPEND acc (CONS (x,1) [])))`;;

let topKFrequent_insertSorted =
  new_recursive_definition list_RECURSION
    `(!pair:int#num.
        topKFrequent_insertSorted
          ([]:(int#num)list) pair = CONS pair []) /\
     (!entry:int#num. !rest:(int#num)list. !pair:int#num.
        topKFrequent_insertSorted (CONS entry rest) pair =
        if SND pair > SND entry then
          CONS pair (CONS entry rest)
        else
          CONS entry
            (topKFrequent_insertSorted rest pair))`;;

let topKFrequent_sortFold =
  new_recursive_definition list_RECURSION
    `(!acc:(int#num)list.
        topKFrequent_sortFold
          ([]:(int#num)list) acc = acc) /\
     (!pair:int#num. !pairs:(int#num)list.
      !acc:(int#num)list.
        topKFrequent_sortFold (CONS pair pairs) acc =
        topKFrequent_sortFold pairs
          (topKFrequent_insertSorted acc pair))`;;

let topKFrequent_take =
  new_recursive_definition num_RECURSION
    `(!xs:(int#num)list.
        topKFrequent_take 0 xs = []) /\
     (!n:num. !xs:(int#num)list.
        topKFrequent_take (SUC n) xs =
        if xs = [] then []
        else
          CONS (HD xs)
            (topKFrequent_take n (TL xs)))`;;

let topKFrequent = new_definition
  `topKFrequent (nums:int list) (k:num) =
     let freqList =
       topKFrequent_buildFreq nums ([]:(int#num)list) in
     let sorted =
       topKFrequent_sortFold freqList ([]:(int#num)list) in
     MAP (\entry:int#num. FST entry)
       (topKFrequent_take k sorted)`;;

let topKFrequent_count =
  new_recursive_definition list_RECURSION
    `(!target:int.
        topKFrequent_count ([]:int list) target = 0) /\
     (!x:int. !xs:int list. !target:int.
        topKFrequent_count (CONS x xs) target =
        if x = target then
          SUC (topKFrequent_count xs target)
        else
          topKFrequent_count xs target)`;;

let topKFrequent_nodup =
  new_recursive_definition list_RECURSION
    `(topKFrequent_nodup ([]:int list) <=> T) /\
     (!x:int. !xs:int list.
        topKFrequent_nodup (CONS x xs) <=>
        ~(MEM x xs) /\ topKFrequent_nodup xs)`;;

let topKFrequent_zipIdxFrom =
  new_recursive_definition list_RECURSION
    `(topKFrequent_zipIdxFrom
        (start:num) ([]:int list) = []) /\
     (!x:int. !xs:int list. !start:num.
        topKFrequent_zipIdxFrom start (CONS x xs) =
        CONS (x,start)
          (topKFrequent_zipIdxFrom (SUC start) xs))`;;

let topKFrequent_zipIdx = new_definition
  `topKFrequent_zipIdx (result:int list) =
     topKFrequent_zipIdxFrom 0 result`;;

let topKFrequent_pairwiseIndexed =
  new_recursive_definition list_RECURSION
    `(!nums:int list.
        topKFrequent_pairwiseIndexed
          nums ([]:(int#num)list) <=> T) /\
     (!indexed:int#num. !rest:(int#num)list. !nums:int list.
        topKFrequent_pairwiseIndexed
          nums (CONS indexed rest) <=>
        ALL
          (\later:int#num.
             SND indexed < SND later
             ==> topKFrequent_count nums (FST indexed) >=
                 topKFrequent_count nums (FST later))
          rest /\
        topKFrequent_pairwiseIndexed nums rest)`;;

let topKFrequent_postcond = new_definition
  `topKFrequent_postcond
      (nums:int list) (k:num) (result:int list) <=>
     LENGTH result = k /\
     ALL (\x:int. MEM x nums) result /\
     topKFrequent_nodup result /\
     ALL
       (\x:int.
          ALL
            (\y:int.
               MEM y result \/
               topKFrequent_count nums x >=
               topKFrequent_count nums y)
            nums)
       result /\
     topKFrequent_pairwiseIndexed
       nums (topKFrequent_zipIdx result)`;;

let topKFrequent_spec_satisfied =
  `!nums:int list. !k:num.
     topKFrequent_precond nums k
     ==> topKFrequent_postcond
           nums k (topKFrequent nums k)`;;
