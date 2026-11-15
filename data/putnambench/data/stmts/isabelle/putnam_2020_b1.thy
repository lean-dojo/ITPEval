theory putnam_2020_b1 imports Complex_Main
begin

definition putnam_2020_b1_solution :: int where
  "putnam_2020_b1_solution \<equiv> 1990"
(* 1990 *)
theorem putnam_2020_b1:
  fixes d :: "nat \<Rightarrow> nat"
  and S :: int
  assumes d0: "d 0 = 0"
  and drec: "\<forall>n::nat>0. d n = n mod 2 + d (n div 2)"
  and hS: "S = (\<Sum>k::nat=1..2020. (-1 :: int)^(d k) * (int k)^3)"
  shows "S mod 2020 = putnam_2020_b1_solution"
  sorry

end
