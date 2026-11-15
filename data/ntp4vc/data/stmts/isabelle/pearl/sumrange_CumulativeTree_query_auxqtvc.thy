theory sumrange_CumulativeTree_query_auxqtvc
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
theorem query_aux'vc:
  fixes t :: "tree"
  fixes a :: "int list"
  fixes i :: "int"
  fixes j :: "int"
  assumes fact0: "is_tree_for t a (low (indexes1 t)) (high (indexes1 t))"
  assumes fact1: "(0 :: int) \<le> low (indexes1 t)"
  assumes fact2: "low (indexes1 t) \<le> i"
  assumes fact3: "i < j"
  assumes fact4: "j \<le> high (indexes1 t)"
  assumes fact5: "high (indexes1 t) \<le> int (length a)"
  shows "case t of Leaf ind \<Rightarrow> True | Node ind l r \<Rightarrow> (\<forall>(o1 :: bool). (if i = low ind then o1 = (if j = high ind then True else False) else o1 = False) \<longrightarrow> \<not>o1 = True \<longrightarrow> (let m :: int = high (indexes1 l) in if j \<le> m then (case t of Leaf _ \<Rightarrow> False | Node _ f f1 \<Rightarrow> f = l \<or> f1 = l) \<and> is_tree_for l a (low (indexes1 l)) (high (indexes1 l)) \<and> (0 :: int) \<le> low (indexes1 l) \<and> low (indexes1 l) \<le> i \<and> i < j \<and> j \<le> high (indexes1 l) \<and> high (indexes1 l) \<le> int (length a) else if m \<le> i then (case t of Leaf _ \<Rightarrow> False | Node _ f f1 \<Rightarrow> f = r \<or> f1 = r) \<and> is_tree_for r a (low (indexes1 r)) (high (indexes1 r)) \<and> (0 :: int) \<le> low (indexes1 r) \<and> low (indexes1 r) \<le> i \<and> i < j \<and> j \<le> high (indexes1 r) \<and> high (indexes1 r) \<le> int (length a) else ((case t of Leaf _ \<Rightarrow> False | Node _ f f1 \<Rightarrow> f = r \<or> f1 = r) \<and> is_tree_for r a (low (indexes1 r)) (high (indexes1 r)) \<and> (0 :: int) \<le> low (indexes1 r) \<and> low (indexes1 r) \<le> m \<and> m < j \<and> j \<le> high (indexes1 r) \<and> high (indexes1 r) \<le> int (length a)) \<and> (case t of Leaf _ \<Rightarrow> False | Node _ f f1 \<Rightarrow> f = l \<or> f1 = l) \<and> is_tree_for l a (low (indexes1 l)) (high (indexes1 l)) \<and> (0 :: int) \<le> low (indexes1 l) \<and> low (indexes1 l) \<le> i \<and> i < m \<and> m \<le> high (indexes1 l) \<and> high (indexes1 l) \<le> int (length a)))"
  and "\<forall>(result :: int). (case t of Leaf ind \<Rightarrow> result = isum ind | Node ind l r \<Rightarrow> (\<exists>(o1 :: bool). (if i = low ind then o1 = (if j = high ind then True else False) else o1 = False) \<and> (if o1 = True then result = isum ind else let m :: int = high (indexes1 l) in if j \<le> m then result = sum a i j else if m \<le> i then result = sum a i j else result = sum a i m + sum a m j))) \<longrightarrow> result = sum a i j"
  sorry
end
