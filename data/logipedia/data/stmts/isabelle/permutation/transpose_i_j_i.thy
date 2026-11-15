(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.transpose_i_j_i, catalog title
  "permutation.transpose_i_j_i": the natural-number transposition swapping
  i and j sends i to j. This file contains no proof.
*)

theory transpose_i_j_i
  imports Main
begin

definition logipedia_transpose :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "logipedia_transpose i j n =
    (if n = i then j else if n = j then i else n)"

theorem transpose_i_j_i:
  "\<forall>i j :: nat. logipedia_transpose i j i = j"
  sorry

end
