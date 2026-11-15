theory leftist_heap_LeftistHeap_is_emptyqtvc
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
theorem is_empty'vc:
  fixes h :: "elt tree"
  fixes result :: "bool"
  assumes fact0: "case h of E \<Rightarrow> result = True | N _ _ _ _ \<Rightarrow> result = False"
  shows "result = True \<longleftrightarrow> leftist_heap_Size.size h = (0 :: int)"
  sorry
end
