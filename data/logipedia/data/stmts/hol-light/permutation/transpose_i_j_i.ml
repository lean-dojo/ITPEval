(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.transpose_i_j_i, catalog title
  "permutation.transpose_i_j_i": transposing two natural numbers sends the
  first selected number to the second. This file contains no proof.
*)

let logipedia_permutation_transpose_i_j_i = new_definition
  `logipedia_permutation_transpose_i_j_i (i:num) (j:num) (n:num) =
     if n = i then j else if n = j then i else n`;;

let statement =
  `!i j:num. logipedia_permutation_transpose_i_j_i i j i = j`;;
