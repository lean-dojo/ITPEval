theory vstte12_tree_reconstruction_TreeReconstruction_buildqtvc
  imports "NTP4Verif.NTP4Verif" "./vstte12_tree_reconstruction_Tree"
begin
theorem build'vc:
  fixes s1 :: "int list"
  shows "\<forall>(t :: tree) (s :: int list). s1 = depths (0 :: int) t @ s \<longrightarrow> (case s of Nil \<Rightarrow> depths (0 :: int) t = s1 | _ \<Rightarrow> (\<forall>(t1 :: tree). \<not>depths (0 :: int) t1 = s1))"
  and "(\<forall>(t :: tree) (s' :: int list). \<not>depths (0 :: int) t @ s' = s1) \<longrightarrow> (\<forall>(t :: tree). \<not>depths (0 :: int) t = s1)"
  sorry
end
