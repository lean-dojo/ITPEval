theory putnam_1984_a2 imports Complex_Main
begin

definition putnam_1984_a2_solution :: "real" where
"putnam_1984_a2_solution \<equiv> 2"
theorem putnam_1984_a2:
  shows "(\<lambda>k::nat.
      (6::real)^(k + 1) /
        ((3^(k + 2) - 2^(k + 2)) * (3^(k + 1) - 2^(k + 1))))
    sums putnam_1984_a2_solution"
  sorry

end
