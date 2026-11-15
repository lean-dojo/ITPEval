theory linked_list_rev_InPlaceRev_appqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref"
begin
typedecl  loc
consts eq_loc :: "loc \<Rightarrow> loc \<Rightarrow> bool"
axiomatization where eq_loc'spec:   "eq_loc l1 l2 = True \<longleftrightarrow> l1 = l2"
  for l1 :: "loc"
  and l2 :: "loc"
consts null :: "loc"
definition disjoint :: "loc list \<Rightarrow> loc list \<Rightarrow> _"
  where "disjoint l1 l2 \<longleftrightarrow> (\<forall>(x :: loc). \<not>(x \<in> set l1 \<and> x \<in> set l2))" for l1 l2
fun no_repet :: "loc list \<Rightarrow> _"
  where "no_repet (Nil :: loc list) = True"
      | "no_repet (Cons x r) = (\<not>x \<in> set r \<and> no_repet r)" for x r
inductive list_seg :: "loc \<Rightarrow> (loc \<Rightarrow> loc) \<Rightarrow> loc list \<Rightarrow> loc \<Rightarrow> bool" where
   list_seg_nil: "list_seg p next (Nil :: loc list) p" for p :: "loc" and "next" :: "loc \<Rightarrow> loc"
 | list_seg_cons: "\<not>p = null \<Longrightarrow> list_seg (next p) next l q \<Longrightarrow> list_seg p next (Cons p l) q" for p :: "loc" and "next" :: "loc \<Rightarrow> loc" and l :: "loc list" and q :: "loc"
theorem app'vc:
  fixes l1 :: "loc"
  fixes "next" :: "loc \<Rightarrow> loc"
  fixes l1M :: "loc list"
  fixes l2 :: "loc"
  fixes l2M :: "loc list"
  assumes fact0: "list_seg l1 next l1M null"
  assumes fact1: "list_seg l2 next l2M null"
  assumes fact2: "disjoint l1M l2M"
  shows "let o1 :: loc = null; o2 :: bool = eq_loc l1 o1 in (o2 = True \<longleftrightarrow> l1 = o1) \<longrightarrow> (if o2 = True then list_seg l2 next (l1M @ l2M) null else (\<not>l1 = null \<and> list_seg l1 next (Nil :: loc list) l1 \<and> list_seg l1 next l1M null \<and> (Nil :: loc list) @ l1M = l1M \<and> disjoint (Nil :: loc list) l1M) \<and> (\<forall>(l1pM :: loc list) (pM :: loc list) (p :: loc). \<not>p = null \<and> list_seg l1 next l1pM p \<and> list_seg p next pM null \<and> l1pM @ pM = l1M \<and> disjoint l1pM pM \<longrightarrow> (let o3 :: loc = null in \<not>p = null \<and> (let o4 :: loc = next p; o5 :: bool = eq_loc o4 o3 in (o5 = True \<longleftrightarrow> o4 = o3) \<longrightarrow> (if \<not>o5 = True then case pM of Nil \<Rightarrow> False | Cons h t \<Rightarrow> \<not>p = null \<and> (case pM of Nil \<Rightarrow> False | Cons _ f \<Rightarrow> f = t) \<and> \<not>next p = null \<and> list_seg l1 next (l1pM @ Cons h (Nil :: loc list)) (next p) \<and> list_seg (next p) next t null \<and> (l1pM @ Cons h (Nil :: loc list)) @ t = l1M \<and> disjoint (l1pM @ Cons h (Nil :: loc list)) t else \<not>p = null \<and> list_seg l1 (next(p := l2)) (l1M @ l2M) null)))))"
  sorry
end
