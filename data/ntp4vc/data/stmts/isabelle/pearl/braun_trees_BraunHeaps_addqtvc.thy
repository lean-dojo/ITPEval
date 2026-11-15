theory braun_trees_BraunHeaps_addqtvc
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
theorem add'vc:
  fixes t :: "elt tree"
  fixes x :: "elt"
  assumes fact0: "heap t"
  assumes fact1: "inv t"
  shows "case t of (Empty :: elt tree) \<Rightarrow> True | Node l y r \<Rightarrow> (case t of (Empty :: elt tree) \<Rightarrow> False | Node f _ f1 \<Rightarrow> f = r \<or> f1 = r) \<and> heap r \<and> inv r"
  and "\<forall>(result :: elt tree). (case t of (Empty :: elt tree) \<Rightarrow> result = Node (Empty :: elt tree) x (Empty :: elt tree) | Node l y r \<Rightarrow> (if le x y then \<exists>(o1 :: elt tree). (heap o1 \<and> inv o1 \<and> occ y o1 = occ y r + (1 :: int) \<and> (\<forall>(e :: elt). \<not>e = y \<longrightarrow> occ e o1 = occ e r) \<and> bintree_Size.size o1 = bintree_Size.size r + (1 :: int)) \<and> result = Node o1 x l else \<exists>(o1 :: elt tree). (heap o1 \<and> inv o1 \<and> occ x o1 = occ x r + (1 :: int) \<and> (\<forall>(e :: elt). \<not>e = x \<longrightarrow> occ e o1 = occ e r) \<and> bintree_Size.size o1 = bintree_Size.size r + (1 :: int)) \<and> result = Node o1 y l)) \<longrightarrow> heap result \<and> inv result \<and> occ x result = occ x t + (1 :: int) \<and> (\<forall>(e :: elt). \<not>e = x \<longrightarrow> occ e result = occ e t) \<and> bintree_Size.size result = bintree_Size.size t + (1 :: int)"
  sorry
end
