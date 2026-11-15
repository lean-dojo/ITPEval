theory sumrange_CumulativeTree_update_auxqtvc
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
theorem update_aux'vc:
  fixes t :: "tree"
  fixes a :: "int list"
  fixes i :: "int"
  fixes v :: "int"
  assumes fact0: "is_tree_for t a (low (indexes1 t)) (high (indexes1 t))"
  assumes fact1: "low (indexes1 t) \<le> i"
  assumes fact2: "i < high (indexes1 t)"
  shows "case t of Leaf ind \<Rightarrow> True | Node ind l r \<Rightarrow> (if i < high (indexes1 l) then (case t of Leaf _ \<Rightarrow> False | Node _ f f1 \<Rightarrow> f = l \<or> f1 = l) \<and> is_tree_for l a (low (indexes1 l)) (high (indexes1 l)) \<and> low (indexes1 l) \<le> i \<and> i < high (indexes1 l) else (case t of Leaf _ \<Rightarrow> False | Node _ f f1 \<Rightarrow> f = r \<or> f1 = r) \<and> is_tree_for r a (low (indexes1 r)) (high (indexes1 r)) \<and> low (indexes1 r) \<le> i \<and> i < high (indexes1 r))"
  and "\<forall>(t' :: tree) (delta :: int). (case t of Leaf ind \<Rightarrow> t' = Leaf (indexes'mk (low ind) (high ind) v) \<and> delta = v - isum ind | Node ind l r \<Rightarrow> (if i < high (indexes1 l) then \<exists>(t'1 :: tree). (low (indexes1 t'1) = low (indexes1 l) \<and> high (indexes1 t'1) = high (indexes1 l) \<and> is_tree_for t'1 (a[nat i := v]) (low (indexes1 t'1)) (high (indexes1 t'1))) \<and> t' = Node (indexes'mk (low ind) (high ind) (isum ind + (v - a ! nat i))) t'1 r \<and> delta = v - a ! nat i else \<exists>(t'1 :: tree). (low (indexes1 t'1) = low (indexes1 r) \<and> high (indexes1 t'1) = high (indexes1 r) \<and> is_tree_for t'1 (a[nat i := v]) (low (indexes1 t'1)) (high (indexes1 t'1))) \<and> t' = Node (indexes'mk (low ind) (high ind) (isum ind + (v - a ! nat i))) l t'1 \<and> delta = v - a ! nat i)) \<longrightarrow> delta = v - a ! nat i \<and> low (indexes1 t') = low (indexes1 t) \<and> high (indexes1 t') = high (indexes1 t) \<and> is_tree_for t' (a[nat i := v]) (low (indexes1 t')) (high (indexes1 t'))"
  sorry
end
