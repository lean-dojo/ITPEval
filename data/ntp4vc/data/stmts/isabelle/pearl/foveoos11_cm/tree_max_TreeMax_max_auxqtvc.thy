theory tree_max_TreeMax_max_auxqtvc
  imports "NTP4Verif.NTP4Verif" "../../lib/isabelle/tree_max_BinTree"
begin
theorem max_aux'vc:
  fixes t :: "tree"
  fixes acc :: "int"
  shows "case t of Null \<Rightarrow> True | Tree v l r \<Rightarrow> (let o1 :: int = max v acc in (case t of Null \<Rightarrow> False | Tree _ f f1 \<Rightarrow> f = r \<or> f1 = r) \<and> (\<forall>(o2 :: int). ge_tree o2 r \<and> o1 \<le> o2 \<and> (o2 = o1 \<or> mem o2 r) \<longrightarrow> (case t of Null \<Rightarrow> False | Tree _ f f1 \<Rightarrow> f = l \<or> f1 = l)))"
  and "\<forall>(result :: int). (case t of Null \<Rightarrow> result = acc | Tree v l r \<Rightarrow> (let o1 :: int = max v acc in \<exists>(o2 :: int). (ge_tree o2 r \<and> o1 \<le> o2 \<and> (o2 = o1 \<or> mem o2 r)) \<and> ge_tree result l \<and> o2 \<le> result \<and> (result = o2 \<or> mem result l))) \<longrightarrow> ge_tree result t \<and> acc \<le> result \<and> (result = acc \<or> mem result t)"
  sorry
end
