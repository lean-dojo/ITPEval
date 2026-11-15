theory sumrange_CumulativeTree_update_aux_complexityqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "./sumrange_ArraySum" "./sumrange_ExtraLemmas"
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
fun depth :: "tree \<Rightarrow> int"
  where "depth (Leaf x) = (1 :: int)" for x
      | "depth (Node x l r) = (1 :: int) + max (depth l) (depth r)" for x l r
theorem update_aux_complexity'vc:
  fixes t :: "tree"
  fixes a :: "int list"
  fixes i :: "int"
  fixes v :: "int"
  fixes c :: "int"
  assumes fact0: "is_tree_for t a (low (indexes1 t)) (high (indexes1 t))"
  assumes fact1: "low (indexes1 t) \<le> i"
  assumes fact2: "i < high (indexes1 t)"
  shows "case t of Leaf ind \<Rightarrow> (let o1 :: tree = Leaf (indexes'mk (low ind) (high ind) v) in c + (1 :: int) - c \<le> depth t \<and> v - isum ind = v - a ! nat i \<and> low (indexes1 o1) = low (indexes1 t) \<and> high (indexes1 o1) = high (indexes1 t) \<and> is_tree_for o1 (a[nat i := v]) (low (indexes1 o1)) (high (indexes1 o1))) | Node ind l r \<Rightarrow> (if i < high (indexes1 l) then ((case t of Leaf _ \<Rightarrow> False | Node _ f f1 \<Rightarrow> f = l \<or> f1 = l) \<and> is_tree_for l a (low (indexes1 l)) (high (indexes1 l)) \<and> low (indexes1 l) \<le> i \<and> i < high (indexes1 l)) \<and> (\<forall>(c1 :: int) (l' :: tree). c1 - (c + (1 :: int)) \<le> depth l \<and> low (indexes1 l') = low (indexes1 l) \<and> high (indexes1 l') = high (indexes1 l) \<and> is_tree_for l' (a[nat i := v]) (low (indexes1 l')) (high (indexes1 l')) \<longrightarrow> c1 - c \<le> depth t \<and> low (indexes1 (Node (indexes'mk (low ind) (high ind) (isum ind + (v - a ! nat i))) l' r)) = low (indexes1 t) \<and> high (indexes1 (Node (indexes'mk (low ind) (high ind) (isum ind + (v - a ! nat i))) l' r)) = high (indexes1 t) \<and> is_tree_for (Node (indexes'mk (low ind) (high ind) (isum ind + (v - a ! nat i))) l' r) (a[nat i := v]) (low (indexes1 (Node (indexes'mk (low ind) (high ind) (isum ind + (v - a ! nat i))) l' r))) (high (indexes1 (Node (indexes'mk (low ind) (high ind) (isum ind + (v - a ! nat i))) l' r)))) else ((case t of Leaf _ \<Rightarrow> False | Node _ f f1 \<Rightarrow> f = r \<or> f1 = r) \<and> is_tree_for r a (low (indexes1 r)) (high (indexes1 r)) \<and> low (indexes1 r) \<le> i \<and> i < high (indexes1 r)) \<and> (\<forall>(c1 :: int) (r' :: tree). c1 - (c + (1 :: int)) \<le> depth r \<and> low (indexes1 r') = low (indexes1 r) \<and> high (indexes1 r') = high (indexes1 r) \<and> is_tree_for r' (a[nat i := v]) (low (indexes1 r')) (high (indexes1 r')) \<longrightarrow> c1 - c \<le> depth t \<and> low (indexes1 (Node (indexes'mk (low ind) (high ind) (isum ind + (v - a ! nat i))) l r')) = low (indexes1 t) \<and> high (indexes1 (Node (indexes'mk (low ind) (high ind) (isum ind + (v - a ! nat i))) l r')) = high (indexes1 t) \<and> is_tree_for (Node (indexes'mk (low ind) (high ind) (isum ind + (v - a ! nat i))) l r') (a[nat i := v]) (low (indexes1 (Node (indexes'mk (low ind) (high ind) (isum ind + (v - a ! nat i))) l r'))) (high (indexes1 (Node (indexes'mk (low ind) (high ind) (isum ind + (v - a ! nat i))) l r')))))"
  sorry
end
