theory vstte12_tree_reconstruction_Harness_harnessqtvc
  imports "NTP4Verif.NTP4Verif" "./vstte12_tree_reconstruction_Tree" "./vstte12_tree_reconstruction_TreeReconstruction"
begin
theorem harness'vc:
  shows "let o1 :: int list = Cons (1 :: int) (Cons (3 :: int) (Cons (3 :: int) (Cons (2 :: int) (Nil :: int list)))) in (\<forall>(result :: tree). depths (0 :: int) result = o1 \<longrightarrow> result = Node Leaf (Node (Node Leaf Leaf) Leaf)) \<and> \<not>(\<forall>(t :: tree). \<not>depths (0 :: int) t = o1)"
  sorry
end
