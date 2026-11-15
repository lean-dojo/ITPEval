theory vstte12_tree_reconstruction_ZipperBased_buildqtvc
  imports "NTP4Verif.NTP4Verif" "./vstte12_tree_reconstruction_Tree"
begin
fun forest_depths :: "(int \<times> tree) list \<Rightarrow> int list"
  where "forest_depths (Nil :: (int \<times> tree) list) = (Nil :: int list)"
      | "forest_depths (Cons (d, t) r) = depths d t @ forest_depths r" for d t r
fun greedy :: "int \<Rightarrow> int \<Rightarrow> tree \<Rightarrow> _"
  where "greedy d d1 t1 = (\<not>d = d1 \<and> (case t1 of Leaf \<Rightarrow> True | Node l1 _ \<Rightarrow> greedy d (d1 + (1 :: int)) l1))" for d d1 t1
inductive g :: "(int \<times> tree) list \<Rightarrow> bool" where
   Gnil: "g (Nil :: (int \<times> tree) list)"
 | Gone: "g (Cons (d, t) (Nil :: (int \<times> tree) list))" for d :: "int" and t :: "tree"
 | Gtwo: "greedy d1 d2 t2 \<Longrightarrow> g (Cons (d1, t1) l) \<Longrightarrow> g (Cons (d2, t2) (Cons (d1, t1) l))" for d1 :: "int" and d2 :: "int" and t2 :: "tree" and t1 :: "tree" and l :: "(int \<times> tree) list"
fun only_leaf :: "(int \<times> tree) list \<Rightarrow> _"
  where "only_leaf (Nil :: (int \<times> tree) list) = True"
      | "only_leaf (Cons (x, t) r) = (t = Leaf \<and> only_leaf r)" for x t r
fun map_leaf :: "int list \<Rightarrow> (int \<times> tree) list"
  where "map_leaf (Nil :: int list) = (Nil :: (int \<times> tree) list)"
      | "map_leaf (Cons d r) = Cons (d, Leaf) (map_leaf r)" for d r
theorem build'vc:
  fixes s :: "int list"
  shows "let o1 :: (int \<times> tree) list = map_leaf s; o2 :: (int \<times> tree) list = (Nil :: (int \<times> tree) list) in (g o2 \<and> (case o1 of Cons (d2, t2) right' \<Rightarrow> only_leaf right' \<and> (case t2 of Node l2 _ \<Rightarrow> g (Cons (d2 + (1 :: int), l2) o2) | Leaf \<Rightarrow> True) | Nil \<Rightarrow> True)) \<and> (\<forall>(result :: tree). depths (0 :: int) result = forest_depths (rev o2 @ o1) \<longrightarrow> depths (0 :: int) result = s) \<and> ((\<forall>(t :: tree). \<not>depths (0 :: int) t = forest_depths (rev o2 @ o1)) \<longrightarrow> (\<forall>(t :: tree). \<not>depths (0 :: int) t = s))"
  sorry
end
