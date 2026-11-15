theory vacid_0_red_black_trees_Vacid0_lookupqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "./vacid_0_red_black_trees_RedBlackTree"
begin
typedecl  rbt
definition inv :: "int \<times> tree \<Rightarrow> _"
  where "inv r \<longleftrightarrow> (case r of (_, t) \<Rightarrow> bst t \<and> (\<exists>(n :: int). rbtree n t))" for r
definition default :: "int \<times> tree \<Rightarrow> int"
  where "default r = (case r of (d, _) \<Rightarrow> d)" for r
definition mem :: "int \<times> tree \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "mem r k v \<longleftrightarrow> (case r of (d, t) \<Rightarrow> memt t k v \<or> v = d \<and> (\<forall>(v' :: int). \<not>memt t k v'))" for r k v
theorem lookup'vc:
  fixes m :: "int"
  fixes m1 :: "tree"
  fixes k :: "int"
  assumes fact0: "inv (m, m1)"
  shows "bst m1"
  and "\<forall>(result :: int). memt m1 k result \<or> (\<forall>(v :: int). \<not>memt m1 k v) \<and> result = m \<longrightarrow> mem (m, m1) k result"
  sorry
end
