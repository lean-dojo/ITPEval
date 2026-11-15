(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_11,
  catalog title "findMajorityElement": an executable first-match search returns
  an integer occurring strictly more than half the time, or -1 when the search
  finds none, together with its precondition and postcondition. This file
  contains no proof.
*)

let countOccurrences =
  new_recursive_definition list_RECURSION
    `(countOccurrences (n:int) [] = 0) /\
     (!x:int. !xs:int list.
        countOccurrences n (CONS x xs) =
        if x = n then SUC (countOccurrences n xs)
        else countOccurrences n xs)`;;

let findMajorityElement_precond = new_definition
  `findMajorityElement_precond (lst:int list) <=> T`;;

let findMajorityElement_scan =
  new_recursive_definition list_RECURSION
    `(findMajorityElement_scan (whole:int list) [] = (-- &1:int)) /\
     (!x:int. !xs:int list. !whole:int list.
        findMajorityElement_scan whole (CONS x xs) =
        if countOccurrences x whole > LENGTH whole DIV 2
        then x
        else findMajorityElement_scan whole xs)`;;

let findMajorityElement = new_definition
  `findMajorityElement (lst:int list) =
     findMajorityElement_scan lst lst`;;

let findMajorityElement_filter_count = new_definition
  `findMajorityElement_filter_count (x:int) (lst:int list) =
     LENGTH (FILTER (\y:int. y = x) lst)`;;

let findMajorityElement_majority = new_definition
  `findMajorityElement_majority (lst:int list) (result:int) <=>
     findMajorityElement_filter_count result lst > LENGTH lst DIV 2 /\
     ALL
       (\x:int.
          findMajorityElement_filter_count x lst <= LENGTH lst DIV 2 \/
          x = result)
       lst`;;

let findMajorityElement_postcond = new_definition
  `findMajorityElement_postcond (lst:int list) (result:int) <=>
     (result = -- &1
      ==> ALL
            (\x:int.
               findMajorityElement_filter_count x lst <= LENGTH lst DIV 2)
            lst \/
          findMajorityElement_majority lst result) /\
     (~(result = -- &1)
      ==> findMajorityElement_majority lst result)`;;

let findMajorityElement_spec_satisfied =
  `!lst:int list.
     findMajorityElement_precond lst
     ==> findMajorityElement_postcond lst (findMajorityElement lst)`;;
