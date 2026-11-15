theory sumrange_CumulativeArray_queryqtvc
  imports "NTP4Verif.NTP4Verif" "./sumrange_ArraySum" "./sumrange_ExtraLemmas"
begin
definition is_cumulative_array_for :: "int list \<Rightarrow> int list \<Rightarrow> _"
  where "is_cumulative_array_for c a \<longleftrightarrow> int (length c) = int (length a) + (1 :: int) \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length c) \<longrightarrow> c ! nat i = sum a (0 :: int) i)" for c a
theorem query'vc:
  fixes c :: "int list"
  fixes a :: "int list"
  fixes i :: "int"
  fixes j :: "int"
  assumes fact0: "is_cumulative_array_for c a"
  assumes fact1: "(0 :: int) \<le> i"
  assumes fact2: "i \<le> j"
  assumes fact3: "j < int (length c)"
  shows "(0 :: int) \<le> i"
  and "i < int (length c)"
  and "(0 :: int) \<le> j"
  and "j < int (length c)"
  and "c ! nat j - c ! nat i = sum a i j"
  sorry
end
