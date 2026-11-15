theory tree_of_list_TreeOfList_tree_of_listqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.bintree_Tree" "Why3STD.bintree_Size" "Why3STD.bintree_Height" "Why3STD.bintree_Inorder" "Why3STD.bintree_InorderLength"
begin
typedecl  elt
theorem tree_of_list'vc:
  fixes l :: "elt list"
  shows "let o1 :: int = int (length l) in ((0 :: int) \<le> o1 \<and> o1 \<le> int (length l)) \<and> (\<forall>(o2 :: elt tree) (o3 :: elt list). inorder o2 @ o3 = l \<and> bintree_Size.size o2 = o1 \<and> ((0 :: int) < o1 \<longrightarrow> (let h :: int = height o2 in (2 :: int) ^\<^sub>i (h - (1 :: int)) \<le> o1 \<and> o1 < (2 :: int) ^\<^sub>i h)) \<longrightarrow> inorder o2 = l \<and> ((0 :: int) < bintree_Size.size o2 \<longrightarrow> (let h :: int = height o2 in (2 :: int) ^\<^sub>i (h - (1 :: int)) \<le> bintree_Size.size o2 \<and> bintree_Size.size o2 < (2 :: int) ^\<^sub>i h)))"
  sorry
end
