theory putnam_1997_a5 imports Complex_Main
begin

definition putnam_1997_a5_solution :: bool where
  "putnam_1997_a5_solution \<equiv> True"
(* True *)
theorem putnam_1997_a5:
  fixes N::"nat\<Rightarrow>nat"
  defines "N \<equiv> \<lambda>n. card {t::nat list. size t = n \<and>
    (\<forall>i \<in> {0..<n}. t!i > 0) \<and>
    (\<Sum>i=0..<n. 1 / real (t!i)) = 1}"
  shows "odd (N 10) \<longleftrightarrow> putnam_1997_a5_solution"
  sorry

end
