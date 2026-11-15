theory binomial_heap_BinomialHeap_get_minqtvc
  imports "NTP4Verif.NTP4Verif"
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
datatype  tree = tree'mk (elem: "elt") (children: "tree list") (rank: "int")
fun size :: "tree list \<Rightarrow> int"
  where "size (Nil :: tree list) = (0 :: int)"
      | "size (Cons (tree'mk x c x0) r) = (1 :: int) + size c + size r" for x c x0 r
fun le_roots :: "elt \<Rightarrow> tree list \<Rightarrow> _"
  where "le_roots e (Nil :: tree list) = True" for e
      | "le_roots e (Cons t r) = (le e (elem t) \<and> le_roots e r)" for e t r
fun heaps :: "tree list \<Rightarrow> _"
  where "heaps (Nil :: tree list) = True"
      | "heaps (Cons (tree'mk e c x) r) = (le_roots e c \<and> heaps c \<and> heaps r)" for e c x r
fun occ :: "elt \<Rightarrow> tree list \<Rightarrow> int"
  where "occ x (Nil :: tree list) = (0 :: int)" for x
      | "occ x (Cons (tree'mk y c x0) r) = (if x = y then 1 :: int else (0 :: int)) + occ x c + occ x r" for x y c x0 r
definition mem :: "elt \<Rightarrow> tree list \<Rightarrow> _"
  where "mem x l \<longleftrightarrow> (0 :: int) < occ x l" for x l
fun has_order :: "int \<Rightarrow> tree list \<Rightarrow> _"
  where "has_order k (Nil :: tree list) = (k = (0 :: int))" for k
      | "has_order k (Cons (tree'mk x c k') r) = (k' = k - (1 :: int) \<and> has_order (k - (1 :: int)) c \<and> has_order (k - (1 :: int)) r)" for k x c k' r
definition binomial_tree :: "tree \<Rightarrow> _"
  where "binomial_tree t \<longleftrightarrow> rank t = int (length (children t)) \<and> has_order (rank t) (children t)" for t
typedecl  heap
fun inv :: "int \<Rightarrow> tree list \<Rightarrow> _"
  where "inv m (Nil :: tree list) = True" for m
      | "inv m (Cons t r) = (let k :: int = rank t in m \<le> k \<and> binomial_tree t \<and> inv (k + (1 :: int)) r)" for m t r
theorem get_min'vc:
  fixes h :: "tree list"
  assumes fact0: "heaps h"
  assumes fact1: "\<not>h = (Nil :: tree list)"
  shows "case h of Nil \<Rightarrow> False | Cons t l \<Rightarrow> (\<forall>(m :: elt) (l1 :: tree list). heaps l1 \<longrightarrow> (case l1 of Nil \<Rightarrow> True | Cons (tree'mk x _ _) r \<Rightarrow> (\<forall>(o1 :: elt). (if le x m then o1 = x else o1 = m) \<longrightarrow> (case l1 of Nil \<Rightarrow> False | Cons _ f \<Rightarrow> f = r) \<and> heaps r)) \<and> (\<forall>(result :: elt). (case l1 of Nil \<Rightarrow> result = m | Cons (tree'mk x _ _) r \<Rightarrow> (\<exists>(o1 :: elt). (if le x m then o1 = x else o1 = m) \<and> (result = o1 \<or> mem result r) \<and> le result o1 \<and> (\<forall>(x1 :: elt). mem x1 r \<longrightarrow> le result x1))) \<longrightarrow> (result = m \<or> mem result l1) \<and> le result m \<and> (\<forall>(x :: elt). mem x l1 \<longrightarrow> le result x))) \<and> heaps l"
  and "\<forall>(result :: elt). (case h of Nil \<Rightarrow> False | Cons t l \<Rightarrow> (let o1 :: elt = elem t in (result = o1 \<or> mem result l) \<and> le result o1 \<and> (\<forall>(x :: elt). mem x l \<longrightarrow> le result x))) \<longrightarrow> mem result h \<and> (\<forall>(x :: elt). mem x h \<longrightarrow> le result x)"
  sorry
end
