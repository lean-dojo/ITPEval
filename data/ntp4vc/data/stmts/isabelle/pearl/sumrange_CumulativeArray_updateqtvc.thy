theory sumrange_CumulativeArray_updateqtvc
  imports "NTP4Verif.NTP4Verif" "./sumrange_ArraySum" "./sumrange_ExtraLemmas"
begin
definition is_cumulative_array_for :: "int list \<Rightarrow> int list \<Rightarrow> _"
  where "is_cumulative_array_for c a \<longleftrightarrow> int (length c) = int (length a) + (1 :: int) \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length c) \<longrightarrow> c ! nat i = sum a (0 :: int) i)" for c a
theorem update'vc:
  fixes c :: "int list"
  fixes a :: "int list"
  fixes i :: "int"
  fixes v :: "int"
  assumes fact0: "is_cumulative_array_for c a"
  assumes fact1: "(0 :: int) \<le> i"
  assumes fact2: "i < int (length a)"
  shows "(0 :: int) \<le> i"
  and "i < int (length c)"
  and "let o1 :: int = i + (1 :: int) in ((0 :: int) \<le> o1 \<and> o1 < int (length c)) \<and> (let incr :: int = v - c ! nat o1 + c ! nat i in ((0 :: int) \<le> i \<and> i < int (length a)) \<and> (length (a[nat i := v]) = length a \<longrightarrow> nth (a[nat i := v]) o nat = (nth a o nat)(i := v) \<longrightarrow> (let o2 :: int = int (length c) - (1 :: int); o3 :: int = i + (1 :: int) in (o3 \<le> o2 + (1 :: int) \<longrightarrow> ((\<forall>(k :: int). o3 \<le> k \<and> k < int (length c) \<longrightarrow> c ! nat k = sum (a[nat i := v]) (0 :: int) k - incr) \<and> (\<forall>(k :: int). (0 :: int) \<le> k \<and> k < o3 \<longrightarrow> c ! nat k = sum (a[nat i := v]) (0 :: int) k)) \<and> (\<forall>(c1 :: int list). length c1 = length c \<longrightarrow> (\<forall>(j :: int). (o3 \<le> j \<and> j \<le> o2) \<and> (\<forall>(k :: int). j \<le> k \<and> k < int (length c1) \<longrightarrow> c1 ! nat k = sum (a[nat i := v]) (0 :: int) k - incr) \<and> (\<forall>(k :: int). (0 :: int) \<le> k \<and> k < j \<longrightarrow> c1 ! nat k = sum (a[nat i := v]) (0 :: int) k) \<longrightarrow> ((0 :: int) \<le> j \<and> j < int (length c1)) \<and> (let o4 :: int = c1 ! nat j + incr in ((0 :: int) \<le> j \<and> j < int (length c1)) \<and> (length (c1[nat j := o4]) = length c1 \<longrightarrow> nth (c1[nat j := o4]) o nat = (nth c1 o nat)(j := o4) \<longrightarrow> (\<forall>(k :: int). j + (1 :: int) \<le> k \<and> k < int (length (c1[nat j := o4])) \<longrightarrow> c1[nat j := o4] ! nat k = sum (a[nat i := v]) (0 :: int) k - incr) \<and> (\<forall>(k :: int). (0 :: int) \<le> k \<and> k < j + (1 :: int) \<longrightarrow> c1[nat j := o4] ! nat k = sum (a[nat i := v]) (0 :: int) k)))) \<and> ((\<forall>(k :: int). o2 + (1 :: int) \<le> k \<and> k < int (length c1) \<longrightarrow> c1 ! nat k = sum (a[nat i := v]) (0 :: int) k - incr) \<and> (\<forall>(k :: int). (0 :: int) \<le> k \<and> k < o2 + (1 :: int) \<longrightarrow> c1 ! nat k = sum (a[nat i := v]) (0 :: int) k) \<longrightarrow> is_cumulative_array_for c1 (a[nat i := v]) \<and> a[nat i := v] ! nat i = v \<and> (\<forall>(k :: int). ((0 :: int) \<le> k \<and> k < int (length (a[nat i := v]))) \<and> \<not>k = i \<longrightarrow> a[nat i := v] ! nat k = a ! nat k)))) \<and> (o2 + (1 :: int) < o3 \<longrightarrow> is_cumulative_array_for c (a[nat i := v]) \<and> a[nat i := v] ! nat i = v \<and> (\<forall>(k :: int). ((0 :: int) \<le> k \<and> k < int (length (a[nat i := v]))) \<and> \<not>k = i \<longrightarrow> a[nat i := v] ! nat k = a ! nat k)))))"
  sorry
end
