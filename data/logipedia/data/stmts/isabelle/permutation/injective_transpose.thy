(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.injective_transpose, catalog title
  "permutation.injective_transpose": swapping any two natural numbers defines
  an injective function on the natural numbers. This file contains no proof.
*)

theory injective_transpose
  imports Main
begin

definition transpose :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "transpose i j n = (if n = i then j else if n = j then i else n)"

theorem injective_transpose:
  "\<forall>i j :: nat. inj (transpose i j)"
  sorry

end
