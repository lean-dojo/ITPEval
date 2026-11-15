theory tree_max_TreeMax_maxqtvc
  imports "NTP4Verif.NTP4Verif" "../../lib/isabelle/tree_max_BinTree"
begin
theorem max'vc:
  fixes t :: "tree"
  assumes fact0: "\<not>t = Null"
  shows "case t of Null \<Rightarrow> False | Tree v l r \<Rightarrow> True"
  and "\<forall>(result :: int). (case t of Null \<Rightarrow> False | Tree v l r \<Rightarrow> (\<exists>(o1 :: int). (ge_tree o1 r \<and> v \<le> o1 \<and> (o1 = v \<or> mem o1 r)) \<and> ge_tree result l \<and> o1 \<le> result \<and> (result = o1 \<or> mem result l))) \<longrightarrow> ge_tree result t \<and> mem result t"
  sorry
end
