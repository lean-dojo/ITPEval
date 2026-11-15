theory tree_height_HeightStack_height_stackqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.bintree_Tree" "Why3STD.bintree_Size" "Why3STD.bintree_Height"
begin
typedecl 'a stack
fun heights :: "(int \<times> 'a tree) list \<Rightarrow> int"
  where "heights (Nil :: (int \<times> 'a tree) list) = (0 :: int)"
      | "heights (Cons (h, t) s') = max (h + height t) (heights s')" for h t s'
fun sizes :: "(int \<times> 'a tree) list \<Rightarrow> int"
  where "sizes (Nil :: (int \<times> 'a tree) list) = (0 :: int)"
      | "sizes (Cons (x, t) s') = bintree_Size.size t + sizes s'" for x t s'
theorem height_stack'vc:
  fixes m :: "int"
  fixes s :: "(int \<times> 'a tree) list"
  assumes fact0: "(0 :: int) \<le> m"
  shows "case s of (Nil :: (int \<times> 'a tree) list) \<Rightarrow> True | Cons (h, (Empty :: 'a tree)) s' \<Rightarrow> ((0 :: int) \<le> sizes s \<and> sizes s' < sizes s \<or> sizes s = sizes s' \<and> (case s of (Nil :: (int \<times> 'a tree) list) \<Rightarrow> False | Cons _ f \<Rightarrow> f = s')) \<and> (0 :: int) \<le> max m h | Cons (h, Node l _ r) s' \<Rightarrow> (let o1 :: (int \<times> 'a tree) list = Cons (h + (1 :: int), l) (Cons (h + (1 :: int), r) s') in ((0 :: int) \<le> sizes s \<and> sizes o1 < sizes s \<or> sizes s = sizes o1 \<and> (case s of (Nil :: (int \<times> 'a tree) list) \<Rightarrow> False | Cons _ f \<Rightarrow> f = o1)) \<and> (0 :: int) \<le> m)"
  and "\<forall>(result :: int). (case s of (Nil :: (int \<times> 'a tree) list) \<Rightarrow> result = m | Cons (h, (Empty :: 'a tree)) s' \<Rightarrow> result = max (max m h) (heights s') | Cons (h, Node l _ r) s' \<Rightarrow> result = max m (heights (Cons (h + (1 :: int), l) (Cons (h + (1 :: int), r) s')))) \<longrightarrow> result = max m (heights s)"
  sorry
end
