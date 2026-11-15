theory braun_trees_BraunHeaps_replace_minqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.bintree_Tree" "Why3STD.bintree_Size" "Why3STD.bintree_Occ"
begin
typedecl  elt
consts le :: "elt \<Rightarrow> elt \<Rightarrow> bool"
axiomatization where Refl:   "le x x"
  for x :: "elt"
axiomatization where Trans:   "le x z"
 if "le x y"
 and "le y z"
  for x :: "elt"
  and y :: "elt"
  and z :: "elt"
axiomatization where Total:   "le x y \<or> le y x"
  for x :: "elt"
  and y :: "elt"
definition le_root :: "elt \<Rightarrow> elt tree \<Rightarrow> _"
  where "le_root e t \<longleftrightarrow> (case t of (Empty :: elt tree) \<Rightarrow> True | Node _ x _ \<Rightarrow> le e x)" for e t
fun heap :: "elt tree \<Rightarrow> _"
  where "heap (Empty :: elt tree) = True"
      | "heap (Node l x r) = (le_root x l \<and> heap l \<and> le_root x r \<and> heap r)" for l x r
consts minimum :: "elt tree \<Rightarrow> elt"
axiomatization where minimum_def:   "minimum (Node l x r) = x"
  for l :: "elt tree"
  and x :: "elt"
  and r :: "elt tree"
definition is_minimum :: "elt \<Rightarrow> elt tree \<Rightarrow> _"
  where "is_minimum x t \<longleftrightarrow> mem x t \<and> (\<forall>(e :: elt). mem e t \<longrightarrow> le x e)" for x t
fun inv :: "elt tree \<Rightarrow> _"
  where "inv (Empty :: elt tree) = True"
      | "inv (Node l x r) = ((bintree_Size.size l = bintree_Size.size r \<or> bintree_Size.size l = bintree_Size.size r + (1 :: int)) \<and> inv l \<and> inv r)" for l x r
consts empty :: "elt tree"
axiomatization where empty'def'0:   "heap empty"
axiomatization where empty'def'1:   "inv empty"
axiomatization where empty'def'2:   "bintree_Size.size empty = (0 :: int)"
axiomatization where empty'def'3:   "\<forall>(e :: elt). \<not>mem e empty"
theorem replace_min'vc:
  fixes t :: "elt tree"
  fixes x :: "elt"
  assumes fact0: "heap t"
  assumes fact1: "inv t"
  assumes fact2: "(0 :: int) < bintree_Size.size t"
  shows "case t of Node l _ r \<Rightarrow> (\<forall>(o1 :: bool). (if le_root x l then o1 = (if le_root x r then True else False) else o1 = False) \<longrightarrow> \<not>o1 = True \<longrightarrow> (heap l \<and> (0 :: int) < bintree_Size.size l) \<and> (if le_root (minimum l) r then (case t of (Empty :: elt tree) \<Rightarrow> False | Node f _ f1 \<Rightarrow> f = l \<or> f1 = l) \<and> heap l \<and> inv l \<and> (0 :: int) < bintree_Size.size l else ((case t of (Empty :: elt tree) \<Rightarrow> False | Node f _ f1 \<Rightarrow> f = r \<or> f1 = r) \<and> heap r \<and> inv r \<and> (0 :: int) < bintree_Size.size r) \<and> (\<forall>(o2 :: elt tree). heap o2 \<and> inv o2 \<and> (if x = minimum r then occ x o2 = occ x r else occ x o2 = occ x r + (1 :: int) \<and> occ (minimum r) o2 = occ (minimum r) r - (1 :: int)) \<and> (\<forall>(e :: elt). \<not>e = x \<longrightarrow> \<not>e = minimum r \<longrightarrow> occ e o2 = occ e r) \<and> bintree_Size.size o2 = bintree_Size.size r \<longrightarrow> heap r \<and> (0 :: int) < bintree_Size.size r))) | (Empty :: elt tree) \<Rightarrow> False"
  and "\<forall>(result :: elt tree). (case t of Node l _ r \<Rightarrow> (\<exists>(o1 :: bool). (if le_root x l then o1 = (if le_root x r then True else False) else o1 = False) \<and> (if o1 = True then result = Node l x r else let lx :: elt = minimum l in if le_root lx r then \<exists>(o2 :: elt tree). (heap o2 \<and> inv o2 \<and> (if x = minimum l then occ x o2 = occ x l else occ x o2 = occ x l + (1 :: int) \<and> occ (minimum l) o2 = occ (minimum l) l - (1 :: int)) \<and> (\<forall>(e :: elt). \<not>e = x \<longrightarrow> \<not>e = minimum l \<longrightarrow> occ e o2 = occ e l) \<and> bintree_Size.size o2 = bintree_Size.size l) \<and> result = Node o2 lx r else \<exists>(o2 :: elt tree). (heap o2 \<and> inv o2 \<and> (if x = minimum r then occ x o2 = occ x r else occ x o2 = occ x r + (1 :: int) \<and> occ (minimum r) o2 = occ (minimum r) r - (1 :: int)) \<and> (\<forall>(e :: elt). \<not>e = x \<longrightarrow> \<not>e = minimum r \<longrightarrow> occ e o2 = occ e r) \<and> bintree_Size.size o2 = bintree_Size.size r) \<and> result = Node l (minimum r) o2)) | (Empty :: elt tree) \<Rightarrow> False) \<longrightarrow> heap result \<and> inv result \<and> (if x = minimum t then occ x result = occ x t else occ x result = occ x t + (1 :: int) \<and> occ (minimum t) result = occ (minimum t) t - (1 :: int)) \<and> (\<forall>(e :: elt). \<not>e = x \<longrightarrow> \<not>e = minimum t \<longrightarrow> occ e result = occ e t) \<and> bintree_Size.size result = bintree_Size.size t"
  sorry
end
