theory binomial_heap_BinomialHeap_mergeqtvc
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
theorem merge'vc:
  fixes h1 :: "tree list"
  fixes k :: "int"
  fixes h2 :: "tree list"
  assumes fact0: "heaps h1"
  assumes fact1: "inv k h1"
  assumes fact2: "heaps h2"
  assumes fact3: "inv k h2"
  shows "case h2 of Nil \<Rightarrow> (case h1 of Nil \<Rightarrow> True | _ \<Rightarrow> True) | Cons x x1 \<Rightarrow> (case h1 of Nil \<Rightarrow> True | Cons x2 x3 \<Rightarrow> (if rank x2 < rank x then let o1 :: int = rank x2 + (1 :: int) in (case h1 of Nil \<Rightarrow> False | Cons _ f \<Rightarrow> f = x3) \<and> heaps x3 \<and> inv o1 x3 \<and> heaps h2 \<and> inv o1 h2 else if rank x < rank x2 then let o1 :: int = rank x + (1 :: int) in (case h2 of Nil \<Rightarrow> False | Cons _ f \<Rightarrow> f = x1) \<and> heaps h1 \<and> inv o1 h1 \<and> heaps x1 \<and> inv o1 x1 else let o1 :: int = rank x2 + (1 :: int) in (((case h1 of Nil \<Rightarrow> False | Cons _ f \<Rightarrow> f = x3) \<or> h1 = x3 \<and> (case h2 of Nil \<Rightarrow> False | Cons _ f \<Rightarrow> f = x1)) \<and> heaps x3 \<and> inv o1 x3 \<and> heaps x1 \<and> inv o1 x1) \<and> (\<forall>(o2 :: tree list). heaps o2 \<and> inv o1 o2 \<and> (\<forall>(x4 :: elt). occ x4 o2 = occ x4 x3 + occ x4 x1) \<longrightarrow> (let o3 :: tree = link x2 x in heaps (Cons o3 (Nil :: tree list)) \<and> binomial_tree o3 \<and> heaps o2 \<and> inv (rank o3) o2))))"
  and "\<forall>(result :: tree list). (case h2 of Nil \<Rightarrow> (case h1 of Nil \<Rightarrow> result = h2 | _ \<Rightarrow> result = h1) | Cons x x1 \<Rightarrow> (case h1 of Nil \<Rightarrow> result = h2 | Cons x2 x3 \<Rightarrow> (if rank x2 < rank x then \<exists>(o1 :: tree list). (heaps o1 \<and> inv (rank x2 + (1 :: int)) o1 \<and> (\<forall>(x4 :: elt). occ x4 o1 = occ x4 x3 + occ x4 h2)) \<and> result = Cons x2 o1 else if rank x < rank x2 then \<exists>(o1 :: tree list). (heaps o1 \<and> inv (rank x + (1 :: int)) o1 \<and> (\<forall>(x4 :: elt). occ x4 o1 = occ x4 h1 + occ x4 x1)) \<and> result = Cons x o1 else \<exists>(o1 :: tree list). (heaps o1 \<and> inv (rank x2 + (1 :: int)) o1 \<and> (\<forall>(x4 :: elt). occ x4 o1 = occ x4 x3 + occ x4 x1)) \<and> (let o2 :: tree = link x2 x in heaps result \<and> inv (rank o2) result \<and> (\<forall>(x4 :: elt). occ x4 result = occ x4 (Cons o2 (Nil :: tree list)) + occ x4 o1))))) \<longrightarrow> heaps result \<and> inv k result \<and> (\<forall>(x :: elt). occ x result = occ x h1 + occ x h2)"
  sorry
end
