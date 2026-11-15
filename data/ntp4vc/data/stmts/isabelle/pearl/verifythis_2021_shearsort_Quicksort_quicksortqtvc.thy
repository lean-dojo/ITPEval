theory verifythis_2021_shearsort_Quicksort_quicksortqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_MapEq" "Why3STD.map_MapExchange" "Why3STD.map_MapPermut" "Why3STD.array_IntArraySorted"
begin
definition qs_partition :: "int list \<Rightarrow> int list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "qs_partition a1 a2 l m r v \<longleftrightarrow> permut_sub' a1 a2 (nat l) (nat r) \<and> (\<forall>(j :: int). l \<le> j \<and> j < m \<longrightarrow> a2 ! nat j < v) \<and> (\<forall>(j :: int). m < j \<and> j < r \<longrightarrow> v \<le> a2 ! nat j) \<and> a2 ! nat m = v" for a1 a2 l m r v
theorem quicksort'vc:
  fixes a :: "int list"
  shows "let o1 :: int = int (length a) in ((0 :: int) \<le> (0 :: int) \<and> (0 :: int) \<le> o1 \<and> o1 \<le> int (length a)) \<and> (\<forall>(a1 :: int list). length a1 = length a \<longrightarrow> sorted_sub1 a1 (0 :: int) o1 \<and> permut_sub' a a1 (0 :: nat) (nat o1) \<longrightarrow> array_IntArraySorted.sorted a1 \<and> a <~~> a1)"
  sorry
end
