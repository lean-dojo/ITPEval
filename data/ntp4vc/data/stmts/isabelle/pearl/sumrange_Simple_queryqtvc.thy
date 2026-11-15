theory sumrange_Simple_queryqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "./sumrange_ArraySum"
begin
theorem query'vc:
  fixes i :: "int"
  fixes j :: "int"
  fixes a :: "int list"
  assumes fact0: "(0 :: int) \<le> i"
  assumes fact1: "i \<le> j"
  assumes fact2: "j \<le> int (length a)"
  shows "let o1 :: int = j - (1 :: int) in (i \<le> o1 + (1 :: int) \<longrightarrow> (0 :: int) = sum a i i \<and> (\<forall>(s :: int). (\<forall>(k :: int). (i \<le> k \<and> k \<le> o1) \<and> s = sum a i k \<longrightarrow> ((0 :: int) \<le> k \<and> k < int (length a)) \<and> s + a ! nat k = sum a i (k + (1 :: int))) \<and> (s = sum a i (o1 + (1 :: int)) \<longrightarrow> s = sum a i j))) \<and> (o1 + (1 :: int) < i \<longrightarrow> (0 :: int) = sum a i j)"
  sorry
end
