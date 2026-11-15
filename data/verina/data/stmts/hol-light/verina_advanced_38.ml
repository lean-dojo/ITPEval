(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_38,
  catalog title "maxCoverageAfterRemovingOne": an executable deletion, sorting,
  interval-merging, and maximum fold computes the largest natural-number span
  obtainable after removing one interval from a nonempty list. This file
  contains no proof.
*)

let maxCoverageAfterRemovingOne_precond = new_definition
  `maxCoverageAfterRemovingOne_precond
      (intervals:(num#num)list) <=>
     0 < LENGTH intervals`;;

let maxCoverageAfterRemovingOne_max = new_definition
  `maxCoverageAfterRemovingOne_max (a:num) (b:num) =
     if a <= b then b else a`;;

let maxCoverageAfterRemovingOne_eraseIdx =
  new_recursive_definition num_RECURSION
    `(!intervals:(num#num)list.
        maxCoverageAfterRemovingOne_eraseIdx 0 intervals =
        if intervals = [] then [] else TL intervals) /\
     (!i:num. !intervals:(num#num)list.
        maxCoverageAfterRemovingOne_eraseIdx (SUC i) intervals =
        if intervals = [] then []
        else
          CONS (HD intervals)
            (maxCoverageAfterRemovingOne_eraseIdx
              i (TL intervals)))`;;

let maxCoverageAfterRemovingOne_insert =
  new_recursive_definition list_RECURSION
    `(!interval:num#num.
        maxCoverageAfterRemovingOne_insert
          interval ([]:(num#num)list) =
        CONS interval []) /\
     (!head:num#num. !tail:(num#num)list. !interval:num#num.
        maxCoverageAfterRemovingOne_insert
          interval (CONS head tail) =
        if FST interval <= FST head then
          CONS interval (CONS head tail)
        else
          CONS head
            (maxCoverageAfterRemovingOne_insert interval tail))`;;

let maxCoverageAfterRemovingOne_sort =
  new_recursive_definition list_RECURSION
    `(maxCoverageAfterRemovingOne_sort ([]:(num#num)list) = []) /\
     (!head:num#num. !tail:(num#num)list.
        maxCoverageAfterRemovingOne_sort (CONS head tail) =
        maxCoverageAfterRemovingOne_insert
          head (maxCoverageAfterRemovingOne_sort tail))`;;

let maxCoverageAfterRemovingOne_mergeStep = new_definition
  `maxCoverageAfterRemovingOne_mergeStep
      (acc:(num#num)list) (current:num#num) =
     if acc = [] then CONS current []
     else
       let previous = HD acc in
       if FST current <= SND previous then
         CONS
           (FST previous,
            maxCoverageAfterRemovingOne_max
              (SND previous) (SND current))
           (TL acc)
       else CONS current acc`;;

let maxCoverageAfterRemovingOne_mergeFold =
  new_recursive_definition list_RECURSION
    `(!acc:(num#num)list.
        maxCoverageAfterRemovingOne_mergeFold
          ([]:(num#num)list) acc = acc) /\
     (!current:num#num. !rest:(num#num)list.
      !acc:(num#num)list.
        maxCoverageAfterRemovingOne_mergeFold
          (CONS current rest) acc =
        maxCoverageAfterRemovingOne_mergeFold rest
          (maxCoverageAfterRemovingOne_mergeStep
            acc current))`;;

let maxCoverageAfterRemovingOne_spanFold =
  new_recursive_definition list_RECURSION
    `(!acc:num.
        maxCoverageAfterRemovingOne_spanFold
          ([]:(num#num)list) acc = acc) /\
     (!interval:num#num. !rest:(num#num)list. !acc:num.
        maxCoverageAfterRemovingOne_spanFold
          (CONS interval rest) acc =
        maxCoverageAfterRemovingOne_spanFold rest
          (acc + (SND interval - FST interval)))`;;

let maxCoverageAfterRemovingOne_coverageAt = new_definition
  `maxCoverageAfterRemovingOne_coverageAt
      (intervals:(num#num)list) (i:num) =
     let remaining =
       maxCoverageAfterRemovingOne_eraseIdx i intervals in
     let sorted =
       maxCoverageAfterRemovingOne_sort remaining in
     let merged =
       maxCoverageAfterRemovingOne_mergeFold sorted [] in
     maxCoverageAfterRemovingOne_spanFold
       (REVERSE merged) 0`;;

let maxCoverageAfterRemovingOne_range =
  new_recursive_definition num_RECURSION
    `(maxCoverageAfterRemovingOne_range 0 = []) /\
     (!n:num.
        maxCoverageAfterRemovingOne_range (SUC n) =
        APPEND
          (maxCoverageAfterRemovingOne_range n)
          (CONS n []))`;;

let maxCoverageAfterRemovingOne_maxFold =
  new_recursive_definition list_RECURSION
    `(!intervals:(num#num)list. !acc:num.
        maxCoverageAfterRemovingOne_maxFold
          ([]:num list) intervals acc = acc) /\
     (!i:num. !indices:num list.
      !intervals:(num#num)list. !acc:num.
        maxCoverageAfterRemovingOne_maxFold
          (CONS i indices) intervals acc =
        maxCoverageAfterRemovingOne_maxFold
          indices intervals
          (maxCoverageAfterRemovingOne_max acc
            (maxCoverageAfterRemovingOne_coverageAt
              intervals i)))`;;

let maxCoverageAfterRemovingOne = new_definition
  `maxCoverageAfterRemovingOne
      (intervals:(num#num)list) =
     let n = LENGTH intervals in
     if n <= 1 then 0
     else
       maxCoverageAfterRemovingOne_maxFold
         (maxCoverageAfterRemovingOne_range n)
         intervals 0`;;

let maxCoverageAfterRemovingOne_postcond = new_definition
  `maxCoverageAfterRemovingOne_postcond
      (intervals:(num#num)list) (result:num) <=>
     ?i:num.
       i < LENGTH intervals /\
       result =
         maxCoverageAfterRemovingOne_coverageAt intervals i /\
       (!j:num.
          j < LENGTH intervals
          ==> maxCoverageAfterRemovingOne_coverageAt intervals j <=
              maxCoverageAfterRemovingOne_coverageAt intervals i)`;;

let maxCoverageAfterRemovingOne_spec_satisfied =
  `!intervals:(num#num)list.
     maxCoverageAfterRemovingOne_precond intervals
     ==> maxCoverageAfterRemovingOne_postcond
           intervals
           (maxCoverageAfterRemovingOne intervals)`;;
