theory putnam_1978_b2 imports Complex_Main
begin

definition putnam_1978_b2_solution :: real where
"putnam_1978_b2_solution \<equiv> 7 / 4"
theorem putnam_1978_b2:
  shows "\<exists>row::nat \<Rightarrow> real.
    (\<forall>i. (\<lambda>j::nat.
      1 / real ((i + 1)^2 * (j + 1) + 2 * (i + 1) * (j + 1)
        + (i + 1) * (j + 1)^2)) sums (row i))
    \<and> row sums putnam_1978_b2_solution"
  sorry

end
