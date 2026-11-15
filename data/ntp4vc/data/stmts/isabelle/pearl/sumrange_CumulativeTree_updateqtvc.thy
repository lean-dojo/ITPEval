theory sumrange_CumulativeTree_updateqtvc
  imports "NTP4Verif.NTP4Verif" "./sumrange_ArraySum" "./sumrange_ExtraLemmas"
begin
datatype  indexes = indexes'mk (low: "int") (high: "int") (isum: "int")
datatype  tree = Leaf "indexes" | Node "indexes" "tree" "tree"
definition indexes1 :: "tree \<Rightarrow> indexes"
  where "indexes1 t = (case t of Leaf ind \<Rightarrow> ind | Node ind _ _ \<Rightarrow> ind)" for t
definition is_indexes_for :: "indexes \<Rightarrow> int list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "is_indexes_for ind a i j \<longleftrightarrow> low ind = i \<and> high ind = j \<and> ((0 :: int) \<le> i \<and> i < j \<and> j \<le> int (length a)) \<and> isum ind = sum a i j" for ind a i j
fun is_tree_for :: "tree \<Rightarrow> int list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "is_tree_for (Leaf ind) a i j = (is_indexes_for ind a i j \<and> j = i + (1 :: int))" for ind a i j
      | "is_tree_for (Node ind l r) a i j = (is_indexes_for ind a i j \<and> i = low (indexes1 l) \<and> j = high (indexes1 r) \<and> (let m :: int = high (indexes1 l) in m = low (indexes1 r) \<and> (i < m \<and> m < j) \<and> m = (i + j) cdiv (2 :: int) \<and> is_tree_for l a i m \<and> is_tree_for r a m j))" for ind l r a i j
theorem update'vc:
  fixes i :: "int"
  fixes a :: "int list"
  fixes t :: "tree"
  fixes v :: "int"
  assumes fact0: "(0 :: int) \<le> i"
  assumes fact1: "i < int (length a)"
  assumes fact2: "is_tree_for t a (0 :: int) (int (length a))"
  shows "is_tree_for t a (low (indexes1 t)) (high (indexes1 t))"
  and "low (indexes1 t) \<le> i"
  and "i < high (indexes1 t)"
  and "\<forall>(t1 :: tree). low (indexes1 t1) = low (indexes1 t) \<and> high (indexes1 t1) = high (indexes1 t) \<and> is_tree_for t1 (a[nat i := v]) (low (indexes1 t1)) (high (indexes1 t1)) \<longrightarrow> ((0 :: int) \<le> i \<and> i < int (length a)) \<and> (length (a[nat i := v]) = length a \<longrightarrow> nth (a[nat i := v]) o nat = (nth a o nat)(i := v) \<longrightarrow> a[nat i := v] ! nat i = v \<and> (\<forall>(k :: int). ((0 :: int) \<le> k \<and> k < int (length (a[nat i := v]))) \<and> \<not>k = i \<longrightarrow> a[nat i := v] ! nat k = a ! nat k) \<and> is_tree_for t1 (a[nat i := v]) (0 :: int) (int (length (a[nat i := v]))))"
  sorry
end
