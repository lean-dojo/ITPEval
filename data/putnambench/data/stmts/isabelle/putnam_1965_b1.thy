theory putnam_1965_b1 imports Complex_Main
"HOL-Analysis.Set_Integral"
"HOL-Analysis.Lebesgue_Measure"
"HOL-Analysis.Interval_Integral"
begin

fun putnam_1965_b1_cube_integral :: "nat \<Rightarrow> (real list \<Rightarrow> real) \<Rightarrow> real" where
"putnam_1965_b1_cube_integral 0 F = F []" |
"putnam_1965_b1_cube_integral (Suc n) F =
  interval_lebesgue_integral lebesgue 0 1
    (\<lambda>x. putnam_1965_b1_cube_integral n (\<lambda>xs. F (x # xs)))"

definition putnam_1965_b1_solution :: "real" where
"putnam_1965_b1_solution \<equiv> 1 / 2"
theorem putnam_1965_b1: 
  shows "filterlim
    (\<lambda> n :: nat. putnam_1965_b1_cube_integral (n + 1)
      (\<lambda>xs. cos (pi / (2 * real (n + 1)) * sum_list xs)^2))
    (nhds putnam_1965_b1_solution) at_top"
  sorry

end
