theory foveoos11_challenge2_MaximumTree_maximumqtvc
  imports "NTP4Verif.NTP4Verif"
begin
datatype  tree = Empty | Node "tree" "int" "tree"
fun size :: "tree \<Rightarrow> int"
  where "size (Empty :: tree) = (0 :: int)"
      | "size (Node l x r) = (1 :: int) + size l + size r" for l x r
fun mem :: "int \<Rightarrow> tree \<Rightarrow> _"
  where "mem x (Empty :: tree) = False" for x
      | "mem x (Node l v r) = (mem x l \<or> x = v \<or> mem x r)" for x l v r
theorem maximum'vc:
  fixes t :: "tree"
  assumes fact0: "\<not>t = (Empty :: tree)"
  shows "case t of (Empty :: tree) \<Rightarrow> False | Node (Empty :: tree) v (Empty :: tree) \<Rightarrow> True | Node (Empty :: tree) v s \<Rightarrow> ((0 :: int) \<le> size t \<and> size s < size t) \<and> \<not>s = (Empty :: tree) | Node s v (Empty :: tree) \<Rightarrow> ((0 :: int) \<le> size t \<and> size s < size t) \<and> \<not>s = (Empty :: tree) | Node l v r \<Rightarrow> (((0 :: int) \<le> size t \<and> size r < size t) \<and> \<not>r = (Empty :: tree)) \<and> (\<forall>(o1 :: int). mem o1 r \<and> (\<forall>(x :: int). mem x r \<longrightarrow> x \<le> o1) \<longrightarrow> ((0 :: int) \<le> size t \<and> size l < size t) \<and> \<not>l = (Empty :: tree))"
  and "\<forall>(result :: int). (case t of (Empty :: tree) \<Rightarrow> False | Node (Empty :: tree) v (Empty :: tree) \<Rightarrow> result = v | Node (Empty :: tree) v s \<Rightarrow> (\<exists>(o1 :: int). (mem o1 s \<and> (\<forall>(x :: int). mem x s \<longrightarrow> x \<le> o1)) \<and> result = max o1 v) | Node s v (Empty :: tree) \<Rightarrow> (\<exists>(o1 :: int). (mem o1 s \<and> (\<forall>(x :: int). mem x s \<longrightarrow> x \<le> o1)) \<and> result = max o1 v) | Node l v r \<Rightarrow> (\<exists>(o1 :: int). (mem o1 r \<and> (\<forall>(x :: int). mem x r \<longrightarrow> x \<le> o1)) \<and> (\<exists>(o2 :: int). (mem o2 l \<and> (\<forall>(x :: int). mem x l \<longrightarrow> x \<le> o2)) \<and> result = max o2 (max v o1)))) \<longrightarrow> mem result t \<and> (\<forall>(x :: int). mem x t \<longrightarrow> x \<le> result)"
  sorry
end
