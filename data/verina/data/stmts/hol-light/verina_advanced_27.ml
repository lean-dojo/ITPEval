(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_27,
  catalog title "longestCommonSubsequence": an executable recursive
  computation returns a longest common subsequence of two Unicode strings,
  with its total precondition and exhaustive-subsequence maximality
  postcondition. This file contains no proof.
*)

let longestCommonSubsequence_validChar = new_definition
  `longestCommonSubsequence_validChar (c:num) <=>
     c < 55296 \/ (57343 < c /\ c < 1114112)`;;

let longestCommonSubsequence_string = new_definition
  `longestCommonSubsequence_string (s:num list) <=>
     ALL longestCommonSubsequence_validChar s`;;

let longestCommonSubsequence_precond = new_definition
  `longestCommonSubsequence_precond
      (s1:num list) (s2:num list) <=> T`;;

let toCharList = new_definition
  `toCharList (s:num list) = s`;;

let fromCharList_fold =
  new_recursive_definition list_RECURSION
    `(!acc:num list.
        fromCharList_fold acc [] = acc) /\
     (!c:num. !cs:num list. !acc:num list.
        fromCharList_fold acc (CONS c cs) =
        fromCharList_fold
          (APPEND acc (CONS c [])) cs)`;;

let fromCharList = new_definition
  `fromCharList (cs:num list) = fromCharList_fold [] cs`;;

let lcsAux_fuel =
  new_recursive_definition num_RECURSION
    `(!xs:num list. !ys:num list.
        lcsAux_fuel 0 xs ys = []) /\
     (!fuel:num. !xs:num list. !ys:num list.
        lcsAux_fuel (SUC fuel) xs ys =
        if xs = [] then []
        else if ys = [] then []
        else
          let x = HD xs in
          let xs' = TL xs in
          let y = HD ys in
          let ys' = TL ys in
          if x = y then
            CONS x (lcsAux_fuel fuel xs' ys')
          else
            let left = lcsAux_fuel fuel xs' ys in
            let right = lcsAux_fuel fuel xs ys' in
            if LENGTH left >= LENGTH right
            then left
            else right)`;;

let lcsAux = new_definition
  `lcsAux (xs:num list) (ys:num list) =
     lcsAux_fuel (LENGTH xs + LENGTH ys) xs ys`;;

let longestCommonSubsequence = new_definition
  `longestCommonSubsequence
      (s1:num list) (s2:num list) =
     let xs = toCharList s1 in
     let ys = toCharList s2 in
     let resultList = lcsAux xs ys in
     fromCharList resultList`;;

let longestCommonSubsequence_subseqFold =
  new_recursive_definition list_RECURSION
    `(!acc:(num list)list.
        longestCommonSubsequence_subseqFold [] acc = acc) /\
     (!x:num. !xs:num list. !acc:(num list)list.
        longestCommonSubsequence_subseqFold (CONS x xs) acc =
        longestCommonSubsequence_subseqFold
          xs
          (APPEND acc
            (MAP (\sub:num list. CONS x sub) acc)))`;;

let longestCommonSubsequence_allSubseq = new_definition
  `longestCommonSubsequence_allSubseq (arr:num list) =
     MAP REVERSE
       (longestCommonSubsequence_subseqFold
         arr (CONS ([]:num list) []))`;;

let longestCommonSubsequence_postcond = new_definition
  `longestCommonSubsequence_postcond
      (s1:num list) (s2:num list) (result:num list) <=>
     let subseqA =
       longestCommonSubsequence_allSubseq s1 in
     let subseqB =
       longestCommonSubsequence_allSubseq s2 in
     let commonSubseq =
       FILTER (\l:num list. MEM l subseqB) subseqA in
     MEM result commonSubseq /\
     ALL (\l:num list. LENGTH l <= LENGTH result) commonSubseq`;;

let longestCommonSubsequence_spec_satisfied =
  `!s1:num list. !s2:num list.
     longestCommonSubsequence_string s1
     ==> longestCommonSubsequence_string s2
     ==> longestCommonSubsequence_precond s1 s2
     ==> longestCommonSubsequence_postcond
           s1 s2 (longestCommonSubsequence s1 s2)`;;
