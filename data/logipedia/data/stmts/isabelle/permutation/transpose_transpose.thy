(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.transpose_transpose, catalog title
  "permutation.transpose_transpose": applying the natural-number
  transposition that swaps i and j twice returns every natural number to
  itself. This file contains no proof.
*)

theory transpose_transpose
  imports Main
begin

definition logipedia_transpose :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "logipedia_transpose i j n =
    (if n = i then j else if n = j then i else n)"

theorem transpose_transpose:
  "\<forall>i j n :: nat.
    logipedia_transpose i j (logipedia_transpose i j n) = n"
  sorry

end
