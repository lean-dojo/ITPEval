theory koda_ruskey_KodaRuskey_mainqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "./koda_ruskey_KodaRuskey_Spec" "./koda_ruskey_Lemmas"
begin
theorem main'vc:
  fixes f0 :: "forest"
  fixes bits :: "color list"
  assumes fact0: "white_forest f0 (nth bits o nat)"
  assumes fact1: "size_forest f0 = int (length bits)"
  assumes fact2: "valid_nums_forest f0 (int (length bits))"
  shows "let o1 :: forest list = Cons f0 (Nil :: forest list) in (size_forest f0 = int (length bits) \<and> valid_nums_forest f0 (int (length bits)) \<and> sub o1 f0 (nth bits o nat) \<and> any_stack o1 (nth bits o nat) \<and> valid_coloring f0 (nth bits o nat)) \<and> (\<forall>(bits1 :: color list) (visited :: (int \<Rightarrow> color) list). length bits1 = length bits \<longrightarrow> (\<forall>(i :: int). \<not>mem_stack i o1 \<longrightarrow> bits1 ! nat i = bits ! nat i) \<and> koda_ruskey_Lemmas.inverse o1 (nth bits o nat) (nth bits1 o nat) \<and> valid_coloring f0 (nth bits1 o nat) \<and> stored_solutions f0 (nth bits1 o nat) o1 [] visited \<longrightarrow> int (length visited) = count_forest f0 \<and> (let n :: int = int (length visited) in \<forall>(j :: int). (0 :: int) \<le> j \<and> j < n \<longrightarrow> valid_coloring f0 (visited ! nat j) \<and> (\<forall>(k :: int). (0 :: int) \<le> k \<and> k < n \<longrightarrow> \<not>j = k \<longrightarrow> \<not>eq_coloring (int (length bits1)) (visited ! nat j) (visited ! nat k))))"
  sorry
end
