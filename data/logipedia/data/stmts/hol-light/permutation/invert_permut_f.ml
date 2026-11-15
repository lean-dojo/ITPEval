(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.invert_permut_f, catalog title
  "permutation.invert_permut_f": a recursively constructed inverse sends the
  image of an index back to that index when the function is injective on the
  natural-number initial segment through n. This file contains no proof.
*)

let logipedia_permutation_injn = new_definition
  `logipedia_permutation_injn (f:num->num) (n:num) <=>
     !i j:num.
       i <= n
       ==> j <= n
       ==> f i = f j
       ==> i = j`;;

let logipedia_permutation_invert_permut =
  new_recursive_definition num_RECURSION
    `(logipedia_permutation_invert_permut
        0 (f:num->num) (m:num) = 0) /\
     (logipedia_permutation_invert_permut
        (SUC n) f m =
          if m = f (SUC n) then SUC n
          else logipedia_permutation_invert_permut n f m)`;;

let statement =
  `!f:num->num.
   !n m:num.
     m <= n
     ==> logipedia_permutation_injn f n
     ==> logipedia_permutation_invert_permut n f (f m) = m`;;
