theory vstte12_tree_reconstruction_Harness_harness2qtvc
  imports "NTP4Verif.NTP4Verif" "./vstte12_tree_reconstruction_Tree" "./vstte12_tree_reconstruction_TreeReconstruction"
begin
theorem harness2'vc:
  fixes x :: "tree"
  shows "\<not>depths (0 :: int) x = Cons (1 :: int) (Cons (3 :: int) (Cons (2 :: int) (Cons (2 :: int) (Nil :: int list))))"
  sorry
end
