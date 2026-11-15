(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_13,
  catalog title "hasChordIntersection": an executable normalization, insertion
  sort, and stack scan detects crossings among chords with distinct numbered
  endpoints, together with its correctness contract. This file contains no
  proof.
*)

let hasChordIntersection_get =
  new_recursive_definition num_RECURSION
    `(!xs:num list.
        hasChordIntersection_get 0 xs =
        if xs = [] then 0 else HD xs) /\
     (!n:num. !xs:num list.
        hasChordIntersection_get (SUC n) xs =
        if xs = [] then 0
        else hasChordIntersection_get n (TL xs))`;;

let hasChordIntersection_first = new_definition
  `hasChordIntersection_first (chord:num list) =
     hasChordIntersection_get 0 chord`;;

let hasChordIntersection_second = new_definition
  `hasChordIntersection_second (chord:num list) =
     hasChordIntersection_get 1 chord`;;

let hasChordIntersection_flatten =
  new_recursive_definition list_RECURSION
    `(hasChordIntersection_flatten ([]:(num list)list) = []) /\
     (!chord:num list. !chords:(num list)list.
        hasChordIntersection_flatten (CONS chord chords) =
        APPEND chord (hasChordIntersection_flatten chords))`;;

let hasChordIntersection_nodup =
  new_recursive_definition list_RECURSION
    `(hasChordIntersection_nodup ([]:num list) <=> T) /\
     (!x:num. !xs:num list.
        hasChordIntersection_nodup (CONS x xs) <=>
        ~MEM x xs /\ hasChordIntersection_nodup xs)`;;

let hasChordIntersection_precond = new_definition
  `hasChordIntersection_precond
      (N:num) (chords:(num list)list) <=>
     2 <= N /\
     LENGTH chords = N /\
     ALL
       (\chord:num list.
          LENGTH chord = 2 /\
          1 <= hasChordIntersection_first chord /\
          hasChordIntersection_first chord <= 2 * N /\
          1 <= hasChordIntersection_second chord /\
          hasChordIntersection_second chord <= 2 * N)
       chords /\
     hasChordIntersection_nodup
       (hasChordIntersection_flatten chords)`;;

let hasChordIntersection_normalizeChord = new_definition
  `hasChordIntersection_normalizeChord (chord:num list) =
     let a = hasChordIntersection_first chord in
     let b = hasChordIntersection_second chord in
     if a > b then CONS b (CONS a [])
     else CONS a (CONS b [])`;;

let hasChordIntersection_normalize = new_definition
  `hasChordIntersection_normalize (chords:(num list)list) =
     MAP hasChordIntersection_normalizeChord chords`;;

let hasChordIntersection_dropWhile =
  new_recursive_definition list_RECURSION
    `(hasChordIntersection_dropWhile (a:num) [] = []) /\
     (!chord:num list. !chords:(num list)list. !a:num.
        hasChordIntersection_dropWhile a (CONS chord chords) =
        if hasChordIntersection_second chord < a
        then hasChordIntersection_dropWhile a chords
        else CONS chord chords)`;;

let hasChordIntersection_insert =
  new_recursive_definition list_RECURSION
    `(hasChordIntersection_insert
        (x:num list) ([]:(num list)list) = CONS x []) /\
     (!y:num list. !ys:(num list)list. !x:num list.
        hasChordIntersection_insert x (CONS y ys) =
        if hasChordIntersection_first x < hasChordIntersection_first y
        then CONS x (CONS y ys)
        else CONS y (hasChordIntersection_insert x ys))`;;

let hasChordIntersection_sort =
  new_recursive_definition list_RECURSION
    `(hasChordIntersection_sort ([]:(num list)list) = []) /\
     (!x:num list. !xs:(num list)list.
        hasChordIntersection_sort (CONS x xs) =
        hasChordIntersection_insert x
          (hasChordIntersection_sort xs))`;;

let hasChordIntersection_check =
  new_recursive_definition list_RECURSION
    `(hasChordIntersection_check
        (stack:(num list)list) [] = F) /\
     (!chord:num list. !rest:(num list)list.
      !stack:(num list)list.
        hasChordIntersection_check stack (CONS chord rest) =
        let a = hasChordIntersection_first chord in
        let b = hasChordIntersection_second chord in
        let newStack = hasChordIntersection_dropWhile a stack in
        if newStack = []
        then hasChordIntersection_check (CONS chord newStack) rest
        else
          let top = HD newStack in
          if hasChordIntersection_second top > a /\
             hasChordIntersection_second top < b
          then T
          else
            hasChordIntersection_check
              (CONS chord newStack) rest)`;;

let hasChordIntersection = new_definition
  `hasChordIntersection (N:num) (chords:(num list)list) =
     let sortedChords =
       hasChordIntersection_normalize chords in
     let sortedChords =
       hasChordIntersection_sort sortedChords in
     hasChordIntersection_check [] sortedChords`;;

let hasChordIntersection_pair = new_definition
  `hasChordIntersection_pair
      (chord1:num list) (chord2:num list) =
     let a1 = hasChordIntersection_first chord1 in
     let b1 = hasChordIntersection_second chord1 in
     let a2 = hasChordIntersection_first chord2 in
     let b2 = hasChordIntersection_second chord2 in
     (a1 < a2 /\ a2 < b1 /\ b1 < b2) \/
     (a2 < a1 /\ a1 < b2 /\ b2 < b1)`;;

let hasChordIntersection_anyWith =
  new_recursive_definition list_RECURSION
    `(hasChordIntersection_anyWith
        (x:num list) ([]:(num list)list) = F) /\
     (!y:num list. !ys:(num list)list. !x:num list.
        hasChordIntersection_anyWith x (CONS y ys) =
        if hasChordIntersection_pair x y
        then T
        else hasChordIntersection_anyWith x ys)`;;

let hasChordIntersection_checkAllPairs =
  new_recursive_definition list_RECURSION
    `(hasChordIntersection_checkAllPairs
        ([]:(num list)list) = F) /\
     (!x:num list. !xs:(num list)list.
        hasChordIntersection_checkAllPairs (CONS x xs) =
        if hasChordIntersection_anyWith x xs
        then T
        else hasChordIntersection_checkAllPairs xs)`;;

let hasChordIntersection_pairwiseNone =
  new_recursive_definition list_RECURSION
    `(hasChordIntersection_pairwiseNone
        ([]:(num list)list) <=> T) /\
     (!x:num list. !xs:(num list)list.
        hasChordIntersection_pairwiseNone (CONS x xs) <=>
        ALL
          (\y:num list. ~hasChordIntersection_pair x y)
          xs /\
        hasChordIntersection_pairwiseNone xs)`;;

let hasChordIntersection_anyScan =
  new_recursive_definition list_RECURSION
    `(hasChordIntersection_anyScan
        (whole:(num list)list) [] = F) /\
     (!x:num list. !xs:(num list)list.
      !whole:(num list)list.
        hasChordIntersection_anyScan whole (CONS x xs) =
        if hasChordIntersection_anyWith x whole
        then T
        else hasChordIntersection_anyScan whole xs)`;;

let hasChordIntersection_any = new_definition
  `hasChordIntersection_any (chords:(num list)list) =
     hasChordIntersection_anyScan chords chords`;;

let hasChordIntersection_postcond = new_definition
  `hasChordIntersection_postcond
      (N:num) (chords:(num list)list) (result:bool) <=>
     let sortedChords =
       hasChordIntersection_normalize chords in
     (hasChordIntersection_pairwiseNone sortedChords
      ==> ~result) /\
     (hasChordIntersection_any sortedChords
      ==> result)`;;

let hasChordIntersection_spec_satisfied =
  `!N:num. !chords:(num list)list.
     hasChordIntersection_precond N chords
     ==> hasChordIntersection_postcond
           N chords (hasChordIntersection N chords)`;;
