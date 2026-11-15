theory leftist_heap_LeftistHeap_delete_minqtvc
  imports "NTP4Verif.NTP4Verif" "./leftist_heap_TreeRank" "./leftist_heap_Size" "./leftist_heap_Occ"
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
typedecl  t
definition le_root :: "elt \<Rightarrow> elt tree \<Rightarrow> _"
  where "le_root e h \<longleftrightarrow> (case h of E \<Rightarrow> True | N _ _ x _ \<Rightarrow> le e x)" for e h
fun is_heap :: "elt tree \<Rightarrow> _"
  where "is_heap (E :: elt tree) = True"
      | "is_heap (N x0 l x r) = (le_root x l \<and> is_heap l \<and> le_root x r \<and> is_heap r)" for x0 l x r
consts minimum :: "elt tree \<Rightarrow> elt"
axiomatization where minimum_def:   "minimum (N s l x r) = x"
  for s :: "int"
  and l :: "elt tree"
  and x :: "elt"
  and r :: "elt tree"
definition is_minimum :: "elt \<Rightarrow> elt tree \<Rightarrow> _"
  where "is_minimum x h \<longleftrightarrow> mem x h \<and> (\<forall>(e :: elt). mem e h \<longrightarrow> le x e)" for x h
fun rank :: "elt tree \<Rightarrow> int"
  where "rank (E :: elt tree) = (0 :: int)"
      | "rank (N x l x0 r) = (1 :: int) + min (rank l) (rank r)" for x l x0 r
fun leftist :: "elt tree \<Rightarrow> _"
  where "leftist (E :: elt tree) = True"
      | "leftist (N s l x r) = (s = rank (N s l x r) \<and> leftist l \<and> leftist r \<and> rank r \<le> rank l)" for s l x r
definition leftist_heap :: "elt tree \<Rightarrow> _"
  where "leftist_heap h \<longleftrightarrow> is_heap h \<and> leftist h" for h
theorem delete_min'vc:
  fixes h :: "elt tree"
  assumes fact0: "(0 :: int) < leftist_heap_Size.size h"
  assumes fact1: "leftist_heap h"
  shows "case h of E \<Rightarrow> False | N _ l _ r \<Rightarrow> leftist_heap l \<and> leftist_heap r"
  and "\<forall>(result :: elt tree). (case h of E \<Rightarrow> False | N _ l _ r \<Rightarrow> leftist_heap_Size.size result = leftist_heap_Size.size l + leftist_heap_Size.size r \<and> (\<forall>(x :: elt). occ x result = occ x l + occ x r) \<and> leftist_heap result) \<longrightarrow> occ (minimum h) result = occ (minimum h) h - (1 :: int) \<and> (\<forall>(x :: elt). \<not>x = minimum h \<longrightarrow> occ x result = occ x h) \<and> leftist_heap_Size.size result = leftist_heap_Size.size h - (1 :: int) \<and> leftist_heap result"
  sorry
end
