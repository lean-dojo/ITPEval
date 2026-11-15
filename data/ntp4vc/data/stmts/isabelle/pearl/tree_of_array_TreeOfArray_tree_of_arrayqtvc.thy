theory tree_of_array_TreeOfArray_tree_of_arrayqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.bintree_Tree" "Why3STD.bintree_Size" "Why3STD.bintree_Height" "Why3STD.bintree_Inorder"
begin
theorem tree_of_array'vc:
  fixes a :: "'a list"
  shows "let o1 :: int = int (length a) in ((0 :: int) \<le> (0 :: int) \<and> (0 :: int) \<le> o1 \<and> o1 \<le> int (length a)) \<and> (\<forall>(result :: 'a tree). (let n :: int = o1 - (0 :: int) in bintree_Size.size result = n \<and> inorder result = drop (0 :: nat) (take (nat o1 - (0 :: nat)) a) \<and> ((0 :: int) < n \<longrightarrow> (let h :: int = height result in (2 :: int) ^\<^sub>i (h - (1 :: int)) \<le> n \<and> n < (2 :: int) ^\<^sub>i h))) \<longrightarrow> inorder result = drop (0 :: nat) (take (length a - (0 :: nat)) a) \<and> ((0 :: int) < bintree_Size.size result \<longrightarrow> (let h :: int = height result in (2 :: int) ^\<^sub>i (h - (1 :: int)) \<le> bintree_Size.size result \<and> bintree_Size.size result < (2 :: int) ^\<^sub>i h)))"
  sorry
end
