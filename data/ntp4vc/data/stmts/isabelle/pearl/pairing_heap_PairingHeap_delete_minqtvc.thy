theory pairing_heap_PairingHeap_delete_minqtvc
  imports "NTP4Verif.NTP4Verif" "./pairing_heap_HeapType" "./pairing_heap_Size" "./pairing_heap_Occ"
begin
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
definition le_tree :: "elt \<Rightarrow> tree \<Rightarrow> _"
  where "le_tree e t \<longleftrightarrow> (case t of T x _ \<Rightarrow> le e x)" for e t
definition le_root :: "elt \<Rightarrow> raw_heap \<Rightarrow> _"
  where "le_root e h \<longleftrightarrow> (case h of E \<Rightarrow> True | H t \<Rightarrow> le_tree e t)" for e h
fun le_roots :: "elt \<Rightarrow> tree list \<Rightarrow> _"
  where "le_roots e (Nil :: tree list) = True" for e
      | "le_roots e (Cons t r) = (le_tree e t \<and> le_roots e r)" for e t r
fun heap :: "raw_heap \<Rightarrow> _"  and heap_tree :: "tree \<Rightarrow> _"  and heap_list :: "tree list \<Rightarrow> _"
  where "heap (E :: raw_heap) = True"
      | "heap (H t) = heap_tree t" for t
      | "heap_tree (T x l) = (le_roots x l \<and> heap_list l)" for x l
      | "heap_list (Nil :: tree list) = True"
      | "heap_list (Cons t r) = (heap_tree t \<and> heap_list r)" for t r
typedecl  heap1
consts h :: "heap1 \<Rightarrow> raw_heap"
axiomatization where heap'invariant:   "heap (h self)"
  for self :: "heap1"
definition heap'eq :: "heap1 \<Rightarrow> heap1 \<Rightarrow> _"
  where "heap'eq a b \<longleftrightarrow> h a = h b" for a b
axiomatization where heap'inj:   "a = b"
 if "heap'eq a b"
  for a :: "heap1"
  and b :: "heap1"
definition size :: "heap1 \<Rightarrow> int"
  where "size hh = size_heap (h hh)" for hh
definition occ :: "elt \<Rightarrow> heap1 \<Rightarrow> int"
  where "occ e hh = occ_heap e (h hh)" for e hh
definition is_minimum_tree :: "elt \<Rightarrow> tree \<Rightarrow> _"
  where "is_minimum_tree x t \<longleftrightarrow> mem_tree x t \<and> (\<forall>(e :: elt). mem_tree e t \<longrightarrow> le x e)" for x t
definition is_minimum :: "elt \<Rightarrow> raw_heap \<Rightarrow> _"
  where "is_minimum x h1 \<longleftrightarrow> mem x h1 \<and> (\<forall>(e :: elt). mem e h1 \<longrightarrow> le x e)" for x h1
consts minimum_tree :: "tree \<Rightarrow> elt"
axiomatization where minimum_tree_def:   "minimum_tree (T x l) = x"
  for x :: "elt"
  and l :: "tree list"
consts minimum :: "raw_heap \<Rightarrow> elt"
axiomatization where minimum_def:   "minimum (H t) = minimum_tree t"
  for t :: "tree"
definition minimum_heap :: "heap1 \<Rightarrow> elt"
  where "minimum_heap hh = minimum (h hh)" for hh
consts empty :: "heap1"
axiomatization where empty'def'0:   "size_heap (h empty) = (0 :: int)"
axiomatization where empty'def'1:   "\<forall>(e :: elt). \<not>mem e (h empty)"
theorem delete_min'vc:
  fixes hh :: "heap1"
  assumes fact0: "(0 :: int) < size_heap (h hh)"
  shows "let o1 :: raw_heap = h hh in (case o1 of E \<Rightarrow> False | H (T _ l) \<Rightarrow> heap_list l) \<and> (\<forall>(result :: heap1). (case o1 of E \<Rightarrow> False | H (T _ l) \<Rightarrow> size_heap (h result) = size_list l \<and> (\<forall>(x :: elt). occ_heap x (h result) = occ_list x l)) \<longrightarrow> occ_heap (minimum (h hh)) (h result) = occ_heap (minimum (h hh)) (h hh) - (1 :: int) \<and> (\<forall>(y :: elt). \<not>y = minimum (h hh) \<longrightarrow> occ_heap y (h result) = occ_heap y (h hh)) \<and> size_heap (h result) = size_heap (h hh) - (1 :: int))"
  sorry
end
