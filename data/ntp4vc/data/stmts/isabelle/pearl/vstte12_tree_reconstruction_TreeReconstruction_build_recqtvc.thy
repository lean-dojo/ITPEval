theory vstte12_tree_reconstruction_TreeReconstruction_build_recqtvc
  imports "NTP4Verif.NTP4Verif" "./vstte12_tree_reconstruction_Tree"
begin
theorem build_rec'vc:
  fixes s :: "int list"
  fixes d :: "int"
  shows "case s of Nil \<Rightarrow> (\<forall>(t :: tree) (s' :: int list). \<not>depths d t @ s' = s) | Cons h t \<Rightarrow> (if h < d then \<forall>(t1 :: tree) (s' :: int list). \<not>depths d t1 @ s' = s else if h = d then s = depths d Leaf @ t else let o1 :: int = d + (1 :: int) in ((0 :: int) \<le> hd s - d \<and> hd s - o1 < hd s - d) \<and> (\<forall>(l :: tree) (s1 :: int list). s = depths o1 l @ s1 \<longrightarrow> (let o2 :: int = d + (1 :: int) in ((0 :: int) \<le> int (length s) \<and> length s1 < length s \<or> length s = length s1 \<and> (0 :: int) \<le> hd s - d \<and> hd s1 - o2 < hd s - d) \<and> (\<forall>(r :: tree) (s2 :: int list). s1 = depths o2 r @ s2 \<longrightarrow> s = depths d (Node l r) @ s2) \<and> ((\<forall>(t1 :: tree) (s' :: int list). \<not>depths o2 t1 @ s' = s1) \<longrightarrow> (\<forall>(t1 :: tree) (s' :: int list). \<not>depths d t1 @ s' = s)))) \<and> ((\<forall>(t1 :: tree) (s' :: int list). \<not>depths o1 t1 @ s' = s) \<longrightarrow> (\<forall>(t1 :: tree) (s' :: int list). \<not>depths d t1 @ s' = s)))"
  sorry
end
