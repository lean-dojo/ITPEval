theory euler001_Euler001_solveqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.int_Div2" "./euler001_DivModHints" "./euler001_TriangularNumbers" "./euler001_SumMultiple"
begin
theorem solve'vc:
  fixes n :: "int"
  assumes fact0: "(1 :: int) \<le> n"
  shows "\<not>(3 :: int) = (0 :: int)"
  and "let n3 :: int = (n - (1 :: int)) cdiv (3 :: int) in \<not>(5 :: int) = (0 :: int) \<and> (let n5 :: int = (n - (1 :: int)) cdiv (5 :: int) in \<not>(15 :: int) = (0 :: int) \<and> (let n15 :: int = (n - (1 :: int)) cdiv (15 :: int) in \<not>(2 :: int) = (0 :: int) \<and> ((3 :: int) * n3 * (n3 + (1 :: int)) + (5 :: int) * n5 * (n5 + (1 :: int)) - (15 :: int) * n15 * (n15 + (1 :: int))) cdiv (2 :: int) = sum_multiple_3_5_lt n))"
  sorry
end
