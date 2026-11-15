(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_47,
  catalog title "mergeIntervals": an executable insertion sort followed by an
  interval-merging fold computes merged integer intervals, with the specified
  validity, coverage, non-overlap, endpoint, and no-spurious-merge contract.
  This file contains no proof.
*)

let mergeIntervals_precond = new_definition
  `mergeIntervals_precond (intervals:(int#int)list) <=>
     ALL
       (\interval:int#int. FST interval <= SND interval)
       intervals`;;

let mergeIntervals_max = new_definition
  `mergeIntervals_max (a:int) (b:int) =
     if a <= b then b else a`;;

let mergeIntervals_insert =
  new_recursive_definition list_RECURSION
    `(!interval:int#int.
        mergeIntervals_insert
          interval ([]:(int#int)list) =
        CONS interval []) /\
     (!head:int#int. !tail:(int#int)list. !interval:int#int.
        mergeIntervals_insert
          interval (CONS head tail) =
        if FST interval <= FST head then
          CONS interval (CONS head tail)
        else
          CONS head (mergeIntervals_insert interval tail))`;;

let mergeIntervals_sort =
  new_recursive_definition list_RECURSION
    `(mergeIntervals_sort ([]:(int#int)list) = []) /\
     (!head:int#int. !tail:(int#int)list.
        mergeIntervals_sort (CONS head tail) =
        mergeIntervals_insert
          head (mergeIntervals_sort tail))`;;

let mergeIntervals_mergeStep = new_definition
  `mergeIntervals_mergeStep
      (acc:(int#int)list) (current:int#int) =
     if acc = [] then
       CONS current []
     else
       let previous = HD acc in
       if FST current <= SND previous then
         CONS
           (FST previous,
            mergeIntervals_max
              (SND previous) (SND current))
           (TL acc)
       else
         CONS current acc`;;

let mergeIntervals_mergeFold =
  new_recursive_definition list_RECURSION
    `(!acc:(int#int)list.
        mergeIntervals_mergeFold
          ([]:(int#int)list) acc =
        acc) /\
     (!current:int#int. !rest:(int#int)list.
      !acc:(int#int)list.
        mergeIntervals_mergeFold
          (CONS current rest) acc =
        mergeIntervals_mergeFold rest
          (mergeIntervals_mergeStep acc current))`;;

let mergeIntervals = new_definition
  `mergeIntervals (intervals:(int#int)list) =
     REVERSE
       (mergeIntervals_mergeFold
         (mergeIntervals_sort intervals) [])`;;

let mergeIntervals_noOverlap =
  new_recursive_definition list_RECURSION
    `(mergeIntervals_noOverlap ([]:(int#int)list) <=> T) /\
     (!interval:int#int. !rest:(int#int)list.
        mergeIntervals_noOverlap (CONS interval rest) <=>
        if rest = [] then T
        else
          SND interval < FST (HD rest) /\
          mergeIntervals_noOverlap rest)`;;

let mergeIntervals_postcond = new_definition
  `mergeIntervals_postcond
      (intervals:(int#int)list)
      (result:(int#int)list) <=>
     let covered =
       ALL
         (\interval:int#int.
            EX
              (\merged:int#int.
                 FST merged <= FST interval /\
                 SND interval <= SND merged)
              result)
         intervals in
     let resultBounded =
       ALL
         (\merged:int#int.
            EX
              (\interval:int#int.
                 FST interval = FST merged)
              intervals /\
            EX
              (\interval:int#int.
                 SND interval = SND merged)
              intervals)
         result in
     let noSpuriousMerge =
       ALL
         (\merged:int#int.
            ALL
              (\interval:int#int.
                 FST interval = FST merged \/
                 EX
                   (\previous:int#int.
                      FST merged <= FST previous /\
                      SND previous <= SND merged /\
                      FST previous < FST interval /\
                      FST interval <= SND previous)
                   intervals)
              (FILTER
                (\interval:int#int.
                   FST merged <= FST interval /\
                   SND interval <= SND merged)
                intervals))
         result in
     covered /\
     mergeIntervals_noOverlap result /\
     resultBounded /\
     noSpuriousMerge`;;

let mergeIntervals_spec_satisfied =
  `!intervals:(int#int)list.
     mergeIntervals_precond intervals
     ==> mergeIntervals_postcond
           intervals (mergeIntervals intervals)`;;
