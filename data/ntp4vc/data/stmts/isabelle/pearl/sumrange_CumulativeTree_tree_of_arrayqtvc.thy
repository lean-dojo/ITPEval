theory sumrange_CumulativeTree_tree_of_arrayqtvc
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
theorem tree_of_array'vc:
  fixes i :: "int"
  fixes j :: "int"
  fixes a :: "int list"
  assumes fact0: "(0 :: int) \<le> i"
  assumes fact1: "i < j"
  assumes fact2: "j \<le> int (length a)"
  shows "let o1 :: int = i + (1 :: int) in (if o1 = j then (0 :: int) \<le> i \<and> i < int (length a) else \<not>(2 :: int) = (0 :: int) \<and> (let m :: int = (i + j) cdiv (2 :: int) in (((0 :: int) \<le> j - i \<and> m - i < j - i) \<and> (0 :: int) \<le> i \<and> i < m \<and> m \<le> int (length a)) \<and> (\<forall>(l :: tree). is_tree_for l a i m \<longrightarrow> ((0 :: int) \<le> j - i \<and> j - m < j - i) \<and> (0 :: int) \<le> m \<and> m < j \<and> j \<le> int (length a)))) \<and> (\<forall>(result :: tree). (if o1 = j then result = Leaf (indexes'mk i j (a ! nat i)) else let m :: int = (i + j) cdiv (2 :: int) in \<exists>(l :: tree). is_tree_for l a i m \<and> (\<exists>(r :: tree). is_tree_for r a m j \<and> result = Node (indexes'mk i j (isum (indexes1 l) + isum (indexes1 r))) l r)) \<longrightarrow> is_tree_for result a i j)"
  sorry
end
