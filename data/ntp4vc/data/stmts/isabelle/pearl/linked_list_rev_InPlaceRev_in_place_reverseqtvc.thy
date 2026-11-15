theory linked_list_rev_InPlaceRev_in_place_reverseqtvc
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
theorem in_place_reverse'vc:
  fixes l :: "loc"
  fixes "next" :: "loc \<Rightarrow> loc"
  fixes lM :: "loc list"
  assumes fact0: "list_seg l next lM null"
  shows "list_seg l next lM null"
  and "list_seg null next (Nil :: loc list) null"
  and "disjoint lM (Nil :: loc list)"
  and "rev lM @ (Nil :: loc list) = rev lM"
  and "\<forall>(rM :: loc list) (r :: loc) (pM :: loc list) (p :: loc) (next1 :: loc \<Rightarrow> loc). list_seg p next1 pM null \<and> list_seg r next1 rM null \<and> disjoint pM rM \<and> rev pM @ rM = rev lM \<longrightarrow> (let o1 :: loc = null; o2 :: bool = eq_loc p o1 in (o2 = True \<longleftrightarrow> p = o1) \<longrightarrow> (if \<not>o2 = True then \<not>p = null \<and> (case pM of Nil \<Rightarrow> False | Cons h t \<Rightarrow> (case pM of Nil \<Rightarrow> False | Cons _ f \<Rightarrow> f = t) \<and> list_seg (next1 p) (next1(p := r)) t null \<and> list_seg p (next1(p := r)) (Cons h rM) null \<and> disjoint t (Cons h rM) \<and> rev t @ Cons h rM = rev lM) else list_seg r next1 (rev lM) null))"
  sorry
end
