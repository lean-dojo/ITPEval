theory verifythis_fm2012_treedel_Treedel_search_tree_delete_minqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "./verifythis_fm2012_treedel_Memory" "Why3STD.bintree_Tree" "Why3STD.bintree_Inorder"
begin
definition root :: "loc tree \<Rightarrow> loc"
  where "root t = (case t of (Empty :: loc tree) \<Rightarrow> null | Node _ p _ \<Rightarrow> p)" for t
fun istree :: "(loc \<Rightarrow> node) \<Rightarrow> loc tree \<Rightarrow> _"
  where "istree m (Empty :: loc tree) = True" for m
      | "istree m (Node l p r) = (\<not>p = null \<and> istree m l \<and> istree m r \<and> root l = left1 (m p) \<and> root r = right1 (m p))" for m l p r
datatype 'a zipper = Top | Left "'a zipper" "'a" "'a tree"
fun zip :: "'a tree \<Rightarrow> 'a zipper \<Rightarrow> 'a tree"
  where "zip t (Top :: 'a zipper) = t" for t
      | "zip t (Left z1 x r) = zip (Node t x r) z1" for t z1 x r
fun inorderz :: "'a zipper \<Rightarrow> 'a list"
  where "inorderz (Top :: 'a zipper) = (Nil :: 'a list)"
      | "inorderz (Left z1 x r) = Cons x (inorder r) @ inorderz z1" for z1 x r
theorem search_tree_delete_min'vc:
  fixes it :: "loc tree"
  fixes mem :: "loc \<Rightarrow> node"
  assumes fact0: "\<not>root it = null"
  assumes fact1: "istree mem it"
  assumes fact2: "distinct (inorder it)"
  shows "\<not>root it = null"
  and "let o1 :: loc = left1 (mem (root it)); o2 :: loc = null in (eq_loc o1 o2 \<longleftrightarrow> o1 = o2) \<longrightarrow> (if eq_loc o1 o2 then \<not>root it = null \<and> \<not>root it = null \<and> (case it of (Empty :: loc tree) \<Rightarrow> False | Node l _ r \<Rightarrow> istree mem r \<and> root r = right1 (mem (root it)) \<and> (case inorder it of Nil \<Rightarrow> False | Cons p l1 \<Rightarrow> data (mem (root it)) = data (mem p) \<and> inorder r = l1)) else \<not>o1 = null \<and> \<not>it = (Empty :: loc tree) \<and> (\<forall>(o3 :: loc tree). (case it of (Empty :: loc tree) \<Rightarrow> False | Node _ _ r \<Rightarrow> o3 = r) \<longrightarrow> \<not>it = (Empty :: loc tree) \<and> (\<forall>(o4 :: loc tree). (case it of (Empty :: loc tree) \<Rightarrow> False | Node l _ _ \<Rightarrow> o4 = l) \<longrightarrow> ((\<not>root it = null \<and> left1 (mem (root it)) = o1) \<and> \<not>o1 = null \<and> (let pt :: loc tree = Node o4 (root it) o3 in istree mem pt \<and> zip pt Top = it)) \<and> (\<forall>(subtree :: loc tree) (ppr :: loc tree) (zipper1 :: loc zipper) (pp :: loc). \<not>pp = null \<and> \<not>left1 (mem pp) = null \<and> (let pt :: loc tree = Node subtree pp ppr in istree mem pt \<and> zip pt zipper1 = it) \<longrightarrow> (let o5 :: loc = null in (eq_loc (left1 (mem (left1 (mem pp)))) o5 \<longleftrightarrow> left1 (mem (left1 (mem pp))) = o5) \<longrightarrow> (if \<not>eq_loc (left1 (mem (left1 (mem pp)))) o5 then \<not>subtree = (Empty :: loc tree) \<and> (\<forall>(o6 :: loc tree). (case subtree of (Empty :: loc tree) \<Rightarrow> False | Node _ _ r \<Rightarrow> o6 = r) \<longrightarrow> \<not>subtree = (Empty :: loc tree) \<and> (\<forall>(o7 :: loc tree). (case subtree of (Empty :: loc tree) \<Rightarrow> False | Node l _ _ \<Rightarrow> o7 = l) \<longrightarrow> \<not>left1 (mem (left1 (mem pp))) = null \<and> (case subtree of (Empty :: loc tree) \<Rightarrow> False | Node f _ f1 \<Rightarrow> f = o7 \<or> f1 = o7) \<and> \<not>left1 (mem pp) = null \<and> \<not>left1 (mem (left1 (mem pp))) = null \<and> (let pt :: loc tree = Node o7 (left1 (mem pp)) o6 in istree mem pt \<and> zip pt (Left zipper1 pp ppr) = it))) else \<not>left1 (mem pp) = null \<and> \<not>left1 (mem pp) = null \<and> \<not>pp = null \<and> (\<forall>(mem1 :: loc \<Rightarrow> node). mem1 pp = (let x_q' :: node = mem pp in node'mk (right1 (mem (left1 (mem pp)))) (right1 x_q') (data x_q')) \<and> (\<forall>(q :: loc). \<not>q = pp \<longrightarrow> mem1 q = mem q) \<longrightarrow> \<not>subtree = (Empty :: loc tree) \<and> (\<forall>(pl :: loc tree). (case subtree of (Empty :: loc tree) \<Rightarrow> False | Node l _ _ \<Rightarrow> pl = l) \<longrightarrow> \<not>subtree = (Empty :: loc tree) \<and> (\<forall>(o6 :: loc tree). (case subtree of (Empty :: loc tree) \<Rightarrow> False | Node _ _ r \<Rightarrow> o6 = r) \<longrightarrow> (\<forall>(p :: loc). data (mem1 p) = data (mem p)) \<and> istree mem1 (zip o6 (Left zipper1 pp ppr)) \<and> root (zip o6 (Left zipper1 pp ppr)) = root it \<and> (case inorder it of Nil \<Rightarrow> False | Cons p l \<Rightarrow> data (mem (left1 (mem pp))) = data (mem1 p) \<and> inorder (zip o6 (Left zipper1 pp ppr)) = l))))))))))"
  sorry
end
