theory quicksort_Shuffle_shuffleqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.map_MapEq" "Why3STD.map_MapExchange" "Why3STD.map_MapPermut" "Why3STD.random_State" "Why3STD.random_Random"
begin
theorem shuffle'vc:
  fixes a :: "int list"
  shows "let o1 :: int = int (length a) - (1 :: int) in ((1 :: int) \<le> o1 + (1 :: int) \<longrightarrow> a <~~> a \<and> (\<forall>(a1 :: int list). length a1 = length a \<longrightarrow> (\<forall>(i :: int). ((1 :: int) \<le> i \<and> i \<le> o1) \<and> a <~~> a1 \<longrightarrow> (let o2 :: int = i + (1 :: int) in (0 :: int) < o2 \<and> (\<forall>(o3 :: int). (0 :: int) \<le> o3 \<and> o3 < o2 \<longrightarrow> (((0 :: int) \<le> i \<and> i < int (length a1)) \<and> (0 :: int) \<le> o3 \<and> o3 < int (length a1)) \<and> (\<forall>(a2 :: int list). length a2 = length a1 \<longrightarrow> list_exchange a1 a2 i o3 \<longrightarrow> a <~~> a2)))))) \<and> (o1 + (1 :: int) < (1 :: int) \<longrightarrow> a <~~> a)"
  sorry
end
