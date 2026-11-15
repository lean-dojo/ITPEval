theory algo64_Algo64_quicksortqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_MapEq" "Why3STD.map_MapExchange" "Why3STD.map_MapPermut" "Why3STD.array_IntArraySorted"
begin
definition qs_partition :: "int list \<Rightarrow> int list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "qs_partition t1 t2 m n i j x \<longleftrightarrow> permut_sub' t1 t2 (nat m) (nat (n + (1 :: int))) \<and> (\<forall>(k :: int). m \<le> k \<and> k \<le> j \<longrightarrow> t2 ! nat k \<le> x) \<and> (\<forall>(k :: int). j < k \<and> k < i \<longrightarrow> t2 ! nat k = x) \<and> (\<forall>(k :: int). i \<le> k \<and> k \<le> n \<longrightarrow> x \<le> t2 ! nat k)" for t1 t2 m n i j x
theorem quicksort'vc:
  fixes m :: "int"
  fixes n :: "int"
  fixes a :: "int list"
  assumes fact0: "(0 :: int) \<le> m"
  assumes fact1: "m \<le> n"
  assumes fact2: "n < int (length a)"
  shows "if m < n then ((0 :: int) \<le> m \<and> m < n \<and> n < int (length a)) \<and> (\<forall>(j :: int) (i :: int) (a1 :: int list). length a1 = length a \<longrightarrow> (m \<le> j \<and> j < i \<and> i \<le> n) \<and> permut_sub' a a1 (nat m) (nat (n + (1 :: int))) \<and> (\<forall>(r :: int). m \<le> r \<and> r \<le> j \<longrightarrow> a1 ! nat r \<le> (42 :: int)) \<and> (\<forall>(r :: int). j < r \<and> r < i \<longrightarrow> a1 ! nat r = (42 :: int)) \<and> (\<forall>(r :: int). i \<le> r \<and> r \<le> n \<longrightarrow> (42 :: int) \<le> a1 ! nat r) \<longrightarrow> (((0 :: int) \<le> n - m \<and> j - m < n - m) \<and> (0 :: int) \<le> m \<and> m \<le> j \<and> j < int (length a1)) \<and> (\<forall>(a2 :: int list). length a2 = length a1 \<longrightarrow> permut_sub' a1 a2 (nat m) (nat (j + (1 :: int))) \<and> sorted_sub1 a2 m (j + (1 :: int)) \<longrightarrow> (((0 :: int) \<le> n - m \<and> n - i < n - m) \<and> (0 :: int) \<le> i \<and> i \<le> n \<and> n < int (length a2)) \<and> (\<forall>(a3 :: int list). length a3 = length a2 \<longrightarrow> permut_sub' a2 a3 (nat i) (nat (n + (1 :: int))) \<and> sorted_sub1 a3 i (n + (1 :: int)) \<longrightarrow> permut_sub' a a3 (nat m) (nat (n + (1 :: int))) \<and> sorted_sub1 a3 m (n + (1 :: int))))) else permut_sub' a a (nat m) (nat (n + (1 :: int))) \<and> sorted_sub1 a m (n + (1 :: int))"
  sorry
end
