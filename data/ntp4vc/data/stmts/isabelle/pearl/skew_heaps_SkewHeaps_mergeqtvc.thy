theory skew_heaps_SkewHeaps_mergeqtvc
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
consts empty :: "elt tree"
axiomatization where empty'def'0:   "heap empty"
axiomatization where empty'def'1:   "bintree_Size.size empty = (0 :: int)"
axiomatization where empty'def'2:   "\<forall>(e :: elt). \<not>mem e empty"
theorem merge'vc:
  fixes t1 :: "elt tree"
  fixes t2 :: "elt tree"
  assumes fact0: "heap t1"
  assumes fact1: "heap t2"
  shows "case t2 of (Empty :: elt tree) \<Rightarrow> (case t1 of (Empty :: elt tree) \<Rightarrow> True | _ \<Rightarrow> True) | Node x x1 x2 \<Rightarrow> (case t1 of (Empty :: elt tree) \<Rightarrow> True | Node x3 x4 x5 \<Rightarrow> (if le x4 x1 then ((0 :: int) \<le> bintree_Size.size t1 + bintree_Size.size t2 \<and> bintree_Size.size x5 + bintree_Size.size t2 < bintree_Size.size t1 + bintree_Size.size t2) \<and> heap x5 \<and> heap t2 else ((0 :: int) \<le> bintree_Size.size t1 + bintree_Size.size t2 \<and> bintree_Size.size x2 + bintree_Size.size t1 < bintree_Size.size t1 + bintree_Size.size t2) \<and> heap x2 \<and> heap t1))"
  and "\<forall>(result :: elt tree). (case t2 of (Empty :: elt tree) \<Rightarrow> (case t1 of (Empty :: elt tree) \<Rightarrow> result = t2 | _ \<Rightarrow> result = t1) | Node x x1 x2 \<Rightarrow> (case t1 of (Empty :: elt tree) \<Rightarrow> result = t2 | Node x3 x4 x5 \<Rightarrow> (if le x4 x1 then \<exists>(o1 :: elt tree). (heap o1 \<and> (\<forall>(e :: elt). occ e o1 = occ e x5 + occ e t2) \<and> bintree_Size.size o1 = bintree_Size.size x5 + bintree_Size.size t2) \<and> result = Node o1 x4 x3 else \<exists>(o1 :: elt tree). (heap o1 \<and> (\<forall>(e :: elt). occ e o1 = occ e x2 + occ e t1) \<and> bintree_Size.size o1 = bintree_Size.size x2 + bintree_Size.size t1) \<and> result = Node o1 x1 x))) \<longrightarrow> heap result \<and> (\<forall>(e :: elt). occ e result = occ e t1 + occ e t2) \<and> bintree_Size.size result = bintree_Size.size t1 + bintree_Size.size t2"
  sorry
end
