(*
  Statement-only formalization of the divisibility-by-3 rule from Hundred
  Theorems item 085. The left side is a base-10 numeral with digits d i, and
  the right side is its digit sum. This file contains no proof.
*)

theory Divisibility_By_3_Rule
  imports Main
begin

theorem divisibility_by_3:
  fixes d :: "nat \<Rightarrow> nat"
    and n :: nat
  shows "(3::nat) dvd (\<Sum>i\<le>n. 10 ^ i * d i) \<longleftrightarrow>
    3 dvd (\<Sum>i\<le>n. d i)"
  sorry

end
