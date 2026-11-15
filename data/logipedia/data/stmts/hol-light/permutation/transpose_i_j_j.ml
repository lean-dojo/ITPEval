(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.transpose_i_j_j, catalog title
  "permutation.transpose_i_j_j": transposing two natural numbers sends the
  second selected number to the first. This file contains no proof.
*)

let logipedia_permutation_transpose_i_j_j = new_definition
  `logipedia_permutation_transpose_i_j_j (i:num) (j:num) (n:num) =
     if n = i then j else if n = j then i else n`;;

let statement =
  `!i j:num. logipedia_permutation_transpose_i_j_j i j j = i`;;
