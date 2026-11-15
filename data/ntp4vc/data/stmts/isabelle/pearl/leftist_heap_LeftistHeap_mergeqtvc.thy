theory leftist_heap_LeftistHeap_mergeqtvc
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
theorem merge'vc:
  fixes h1 :: "elt tree"
  fixes h2 :: "elt tree"
  assumes fact0: "leftist_heap h1"
  assumes fact1: "leftist_heap h2"
  shows "case h2 of E \<Rightarrow> (case h1 of E \<Rightarrow> True | _ \<Rightarrow> True) | N x x1 x2 x3 \<Rightarrow> (case h1 of E \<Rightarrow> True | N x4 x5 x6 x7 \<Rightarrow> (if le x6 x2 then (((0 :: int) \<le> leftist_heap_Size.size h1 + leftist_heap_Size.size h2 \<and> leftist_heap_Size.size x7 + leftist_heap_Size.size h2 < leftist_heap_Size.size h1 + leftist_heap_Size.size h2) \<and> leftist_heap x7 \<and> leftist_heap h2) \<and> (\<forall>(o1 :: elt tree). leftist_heap_Size.size o1 = leftist_heap_Size.size x7 + leftist_heap_Size.size h2 \<and> (\<forall>(x8 :: elt). occ x8 o1 = occ x8 x7 + occ x8 h2) \<and> leftist_heap o1 \<longrightarrow> (leftist_heap o1 \<and> leftist_heap x5) \<and> le_root x6 x5 \<and> le_root x6 o1) else (((0 :: int) \<le> leftist_heap_Size.size h1 + leftist_heap_Size.size h2 \<and> leftist_heap_Size.size h1 + leftist_heap_Size.size x3 < leftist_heap_Size.size h1 + leftist_heap_Size.size h2) \<and> leftist_heap h1 \<and> leftist_heap x3) \<and> (\<forall>(o1 :: elt tree). leftist_heap_Size.size o1 = leftist_heap_Size.size h1 + leftist_heap_Size.size x3 \<and> (\<forall>(x8 :: elt). occ x8 o1 = occ x8 h1 + occ x8 x3) \<and> leftist_heap o1 \<longrightarrow> (leftist_heap o1 \<and> leftist_heap x1) \<and> le_root x2 x1 \<and> le_root x2 o1)))"
  and "\<forall>(result :: elt tree). (case h2 of E \<Rightarrow> (case h1 of E \<Rightarrow> result = h1 | _ \<Rightarrow> result = h1) | N x x1 x2 x3 \<Rightarrow> (case h1 of E \<Rightarrow> result = h2 | N x4 x5 x6 x7 \<Rightarrow> (if le x6 x2 then \<exists>(o1 :: elt tree). (leftist_heap_Size.size o1 = leftist_heap_Size.size x7 + leftist_heap_Size.size h2 \<and> (\<forall>(x8 :: elt). occ x8 o1 = occ x8 x7 + occ x8 h2) \<and> leftist_heap o1) \<and> leftist_heap result \<and> minimum result = x6 \<and> leftist_heap_Size.size result = (1 :: int) + leftist_heap_Size.size x5 + leftist_heap_Size.size o1 \<and> occ x6 result = (1 :: int) + occ x6 x5 + occ x6 o1 \<and> (\<forall>(y :: elt). \<not>x6 = y \<longrightarrow> occ y result = occ y x5 + occ y o1) else \<exists>(o1 :: elt tree). (leftist_heap_Size.size o1 = leftist_heap_Size.size h1 + leftist_heap_Size.size x3 \<and> (\<forall>(x8 :: elt). occ x8 o1 = occ x8 h1 + occ x8 x3) \<and> leftist_heap o1) \<and> leftist_heap result \<and> minimum result = x2 \<and> leftist_heap_Size.size result = (1 :: int) + leftist_heap_Size.size x1 + leftist_heap_Size.size o1 \<and> occ x2 result = (1 :: int) + occ x2 x1 + occ x2 o1 \<and> (\<forall>(y :: elt). \<not>x2 = y \<longrightarrow> occ y result = occ y x1 + occ y o1)))) \<longrightarrow> leftist_heap_Size.size result = leftist_heap_Size.size h1 + leftist_heap_Size.size h2 \<and> (\<forall>(x :: elt). occ x result = occ x h1 + occ x h2) \<and> leftist_heap result"
  sorry
end
