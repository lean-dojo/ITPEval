(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_55,
  catalog title "mostFrequent": an executable frequency-map fold returns the
  most frequent integer in a nonempty list, breaking ties by first occurrence,
  together with its full correctness contract. This file contains no proof.
*)

let mostFrequent_precond = new_definition
  `mostFrequent_precond (xs:int list) <=>
     ~(xs = [])`;;

let countMap_lookup =
  new_recursive_definition list_RECURSION
    `(!key:int.
        countMap_lookup ([]:(int#num)list) key = 0) /\
     (!entry:int#num. !rest:(int#num)list. !key:int.
        countMap_lookup (CONS entry rest) key =
        if FST entry = key then SND entry
        else countMap_lookup rest key)`;;

let countMap_insert =
  new_recursive_definition list_RECURSION
    `(!key:int. !value:num.
        countMap_insert ([]:(int#num)list) key value =
        CONS (key,value) []) /\
     (!entry:int#num. !rest:(int#num)list.
      !key:int. !value:num.
        countMap_insert (CONS entry rest) key value =
        if FST entry = key then
          CONS (key,value) rest
        else
          CONS entry (countMap_insert rest key value))`;;

let countMap_fold =
  new_recursive_definition list_RECURSION
    `(!m:(int#num)list.
        countMap_fold ([]:int list) m = m) /\
     (!x:int. !xs:int list. !m:(int#num)list.
        countMap_fold (CONS x xs) m =
        let current = countMap_lookup m x in
        countMap_fold xs
          (countMap_insert m x (current + 1)))`;;

let countMap = new_definition
  `countMap (xs:int list) =
     countMap_fold xs ([]:(int#num)list)`;;

let getMaxFrequency_fold =
  new_recursive_definition list_RECURSION
    `(!acc:num.
        getMaxFrequency_fold ([]:(int#num)list) acc = acc) /\
     (!entry:int#num. !rest:(int#num)list. !acc:num.
        getMaxFrequency_fold (CONS entry rest) acc =
        getMaxFrequency_fold rest
          (if SND entry > acc then SND entry else acc))`;;

let getMaxFrequency = new_definition
  `getMaxFrequency (m:(int#num)list) =
     getMaxFrequency_fold m 0`;;

let getCandidates =
  new_recursive_definition list_RECURSION
    `(!maxFreq:num.
        getCandidates ([]:(int#num)list) maxFreq = []) /\
     (!entry:int#num. !rest:(int#num)list. !maxFreq:num.
        getCandidates (CONS entry rest) maxFreq =
        if SND entry = maxFreq then
          CONS (FST entry) (getCandidates rest maxFreq)
        else
          getCandidates rest maxFreq)`;;

let getFirstWithFreq =
  new_recursive_definition list_RECURSION
    `(!candidates:int list.
        getFirstWithFreq ([]:int list) candidates = (&0:int)) /\
     (!x:int. !xs:int list. !candidates:int list.
        getFirstWithFreq (CONS x xs) candidates =
        if MEM x candidates then x
        else getFirstWithFreq xs candidates)`;;

let mostFrequent = new_definition
  `mostFrequent (xs:int list) =
     let freqMap = countMap xs in
     let maxF = getMaxFrequency freqMap in
     let candidates = getCandidates freqMap maxF in
     getFirstWithFreq xs candidates`;;

let mostFrequent_count =
  new_recursive_definition list_RECURSION
    `(!target:int.
        mostFrequent_count ([]:int list) target = 0) /\
     (!x:int. !xs:int list. !target:int.
        mostFrequent_count (CONS x xs) target =
        if x = target then
          SUC (mostFrequent_count xs target)
        else
          mostFrequent_count xs target)`;;

let mostFrequent_headOption =
  new_recursive_definition list_RECURSION
    `(mostFrequent_headOption ([]:int list) = (NONE:int option)) /\
     (!x:int. !xs:int list.
        mostFrequent_headOption (CONS x xs) = SOME x)`;;

let mostFrequent_postcond = new_definition
  `mostFrequent_postcond (xs:int list) (result:int) <=>
     let count = \x:int. mostFrequent_count xs x in
     MEM result xs /\
     ALL (\x:int. count x <= count result) xs /\
     mostFrequent_headOption
       (FILTER (\x:int. count x = count result) xs) =
       SOME result`;;

let mostFrequent_spec_satisfied =
  `!xs:int list.
     mostFrequent_precond xs
     ==> mostFrequent_postcond xs (mostFrequent xs)`;;
