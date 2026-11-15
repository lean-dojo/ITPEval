theory binomial_heap_BinomialHeap_extract_minqtvc
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
definition link :: "tree \<Rightarrow> tree \<Rightarrow> tree"
  where "link t1 t2 = (if le (elem t1) (elem t2) then tree'mk (elem t1) (Cons t2 (children t1)) (rank t1 + (1 :: int)) else tree'mk (elem t2) (Cons t1 (children t2)) (rank t2 + (1 :: int)))" for t1 t2
theorem extract_min'vc:
  fixes h :: "tree list"
  assumes fact0: "heaps h"
  assumes fact1: "inv (0 :: int) h"
  assumes fact2: "\<not>h = (Nil :: tree list)"
  shows "heaps h"
  and "inv (0 :: int) h"
  and "\<not>h = (Nil :: tree list)"
  and "\<forall>(t :: tree) (h' :: tree list). heaps (Cons t (Nil :: tree list)) \<and> heaps h' \<and> inv (0 :: int) h' \<and> le_roots (elem t) h \<and> binomial_tree t \<and> (\<forall>(x :: elt). occ x h = occ x (Cons t (Nil :: tree list)) + occ x h') \<longrightarrow> (let o1 :: tree list = rev (children t) in heaps o1 \<and> inv (0 :: int) o1 \<and> heaps h' \<and> inv (0 :: int) h') \<and> (\<forall>(h'1 :: tree list). heaps h'1 \<and> inv (0 :: int) h'1 \<and> (\<forall>(x :: elt). occ x h'1 = occ x (rev (children t)) + occ x h') \<longrightarrow> heaps h'1 \<and> inv (0 :: int) h'1 \<and> occ (elem t) h'1 = occ (elem t) h - (1 :: int) \<and> (\<forall>(x :: elt). \<not>x = elem t \<longrightarrow> occ x h'1 = occ x h))"
  sorry
end
