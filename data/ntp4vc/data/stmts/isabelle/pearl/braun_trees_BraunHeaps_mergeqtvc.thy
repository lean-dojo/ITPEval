theory braun_trees_BraunHeaps_mergeqtvc
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
theorem merge'vc:
  fixes l :: "elt tree"
  fixes r :: "elt tree"
  assumes fact0: "heap l"
  assumes fact1: "heap r"
  assumes fact2: "inv l"
  assumes fact3: "inv r"
  assumes fact4: "bintree_Size.size r \<le> bintree_Size.size l"
  assumes fact5: "bintree_Size.size l \<le> bintree_Size.size r + (1 :: int)"
  shows "case r of (Empty :: elt tree) \<Rightarrow> (case l of (Empty :: elt tree) \<Rightarrow> True | _ \<Rightarrow> True) | Node x x1 x2 \<Rightarrow> (case l of Node x3 x4 x5 \<Rightarrow> (if le x4 x1 then ((0 :: int) \<le> bintree_Size.size l + bintree_Size.size r \<and> bintree_Size.size x3 + bintree_Size.size x5 < bintree_Size.size l + bintree_Size.size r) \<and> (heap x3 \<and> heap x5) \<and> (inv x3 \<and> inv x5) \<and> bintree_Size.size x5 \<le> bintree_Size.size x3 \<and> bintree_Size.size x3 \<le> bintree_Size.size x5 + (1 :: int) else (heap l \<and> inv l \<and> (0 :: int) < bintree_Size.size l) \<and> (\<forall>(x6 :: elt) (l1 :: elt tree). heap l1 \<and> inv l1 \<and> bintree_Size.size l1 = bintree_Size.size l - (1 :: int) \<and> occ x6 l1 = occ x6 l - (1 :: int) \<and> (\<forall>(x7 :: elt). \<not>x7 = x6 \<longrightarrow> occ x7 l1 = occ x7 l) \<longrightarrow> heap r \<and> inv r \<and> (0 :: int) < bintree_Size.size r)) | (Empty :: elt tree) \<Rightarrow> False)"
  and "\<forall>(result :: elt tree). (case r of (Empty :: elt tree) \<Rightarrow> (case l of (Empty :: elt tree) \<Rightarrow> result = l | _ \<Rightarrow> result = l) | Node x x1 x2 \<Rightarrow> (case l of Node x3 x4 x5 \<Rightarrow> (if le x4 x1 then \<exists>(o1 :: elt tree). (heap o1 \<and> inv o1 \<and> (\<forall>(e :: elt). occ e o1 = occ e x3 + occ e x5) \<and> bintree_Size.size o1 = bintree_Size.size x3 + bintree_Size.size x5) \<and> result = Node r x4 o1 else \<exists>(e :: elt) (t' :: elt tree). (heap t' \<and> inv t' \<and> bintree_Size.size t' = bintree_Size.size l - (1 :: int) \<and> occ e t' = occ e l - (1 :: int) \<and> (\<forall>(x6 :: elt). \<not>x6 = e \<longrightarrow> occ x6 t' = occ x6 l)) \<and> (\<exists>(o1 :: elt tree). (heap o1 \<and> inv o1 \<and> (if e = minimum r then occ e o1 = occ e r else occ e o1 = occ e r + (1 :: int) \<and> occ (minimum r) o1 = occ (minimum r) r - (1 :: int)) \<and> (\<forall>(e1 :: elt). \<not>e1 = e \<longrightarrow> \<not>e1 = minimum r \<longrightarrow> occ e1 o1 = occ e1 r) \<and> bintree_Size.size o1 = bintree_Size.size r) \<and> result = Node o1 x1 t')) | (Empty :: elt tree) \<Rightarrow> False)) \<longrightarrow> heap result \<and> inv result \<and> (\<forall>(e :: elt). occ e result = occ e l + occ e r) \<and> bintree_Size.size result = bintree_Size.size l + bintree_Size.size r"
  sorry
end
