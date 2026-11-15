(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_50,
  catalog title "mergeSorted": an executable index-and-accumulator merge of
  two sorted natural-number arrays, followed by suffix drains, with a
  sorted-permutation correctness contract. This file contains no proof.
*)

let mergeSorted_precond = new_definition
  `mergeSorted_precond
      (a1:num list) (a2:num list) <=>
     PAIRWISE (\x y:num. x <= y) a1 /\
     PAIRWISE (\x y:num. x <= y) a2`;;

let mergeSorted_mergeLoopFuel =
  new_recursive_definition num_RECURSION
    `(!a1:num list. !a2:num list. !i:num. !j:num.
      !result:num list.
        mergeSorted_mergeLoopFuel 0 a1 a2 i j result =
        (i,(j,result))) /\
     (!fuel:num. !a1:num list. !a2:num list.
      !i:num. !j:num. !result:num list.
        mergeSorted_mergeLoopFuel (SUC fuel) a1 a2 i j result =
        if i < LENGTH a1 /\ j < LENGTH a2 then
          if EL i a1 <= EL j a2 then
            mergeSorted_mergeLoopFuel fuel a1 a2
              (i + 1) j
              (APPEND result (CONS (EL i a1) []))
          else
            mergeSorted_mergeLoopFuel fuel a1 a2
              i (j + 1)
              (APPEND result (CONS (EL j a2) []))
        else
          (i,(j,result)))`;;

let mergeSorted_mergeLoop = new_definition
  `mergeSorted_mergeLoop
      (a1:num list) (a2:num list)
      (i:num) (j:num) (result:num list) =
     mergeSorted_mergeLoopFuel
       ((LENGTH a1 - i) + (LENGTH a2 - j))
       a1 a2 i j result`;;

let mergeSorted_drainFuel =
  new_recursive_definition num_RECURSION
    `(!arr:num list. !i:num. !result:num list.
        mergeSorted_drainFuel 0 arr i result = result) /\
     (!fuel:num. !arr:num list. !i:num. !result:num list.
        mergeSorted_drainFuel (SUC fuel) arr i result =
        if i < LENGTH arr then
          mergeSorted_drainFuel fuel arr (i + 1)
            (APPEND result (CONS (EL i arr) []))
        else
          result)`;;

let mergeSorted_drain = new_definition
  `mergeSorted_drain
      (arr:num list) (i:num) (result:num list) =
     mergeSorted_drainFuel (LENGTH arr - i) arr i result`;;

let mergeSorted = new_definition
  `mergeSorted (a1:num list) (a2:num list) =
     let loopState =
       mergeSorted_mergeLoop a1 a2 0 0 [] in
     let i = FST loopState in
     let j = FST (SND loopState) in
     let merged = SND (SND loopState) in
     let withA1 = mergeSorted_drain a1 i merged in
     mergeSorted_drain a2 j withA1`;;

let mergeSorted_count = new_definition
  `mergeSorted_count (z:num) (xs:num list) =
     LENGTH (FILTER (\x:num. x = z) xs)`;;

let mergeSorted_isPerm = new_definition
  `mergeSorted_isPerm
      (xs:num list) (ys:num list) <=>
     !z:num.
       mergeSorted_count z xs =
       mergeSorted_count z ys`;;

let mergeSorted_postcond = new_definition
  `mergeSorted_postcond
      (a1:num list) (a2:num list)
      (result:num list) <=>
     PAIRWISE (\x y:num. x <= y) result /\
     mergeSorted_isPerm result (APPEND a1 a2)`;;

let mergeSorted_spec_satisfied =
  `!a1:num list. !a2:num list.
     mergeSorted_precond a1 a2
     ==> mergeSorted_postcond
           a1 a2 (mergeSorted a1 a2)`;;
