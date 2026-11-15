theory putnam_2015_b6 imports Complex_Main
"HOL-Analysis.Infinite_Sum"
begin

definition putnam_2015_b6_solution :: real where
  "putnam_2015_b6_solution \<equiv> pi^2 / 16"
(* pi^2 / 16 *)
theorem putnam_2015_b6:
  fixes A :: "nat \<Rightarrow> nat"
  assumes hA: "\<forall>k::nat>0.
    A k = card {j::nat. odd j \<and> j dvd k \<and> real j < sqrt (2 * real k)}"
  shows "(\<lambda>n::nat.
    (-1 :: real)^n * (real (A (n + 1)) / real (n + 1)))
      sums putnam_2015_b6_solution"
  sorry

end
