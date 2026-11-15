theory verifythis_2021_dll_to_bst_Top_size_altqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.ocaml_Exceptions" "Why3STD.bintree_Tree" "Why3STD.bintree_Size" "Why3STD.bintree_Height"
begin
typedecl  loc
typedecl 'v t
consts to_fmap :: "'v t \<Rightarrow> (loc, 'v) fmap"
consts null :: "loc"
definition valid :: "(loc, loc) fmap \<Rightarrow> (loc, loc) fmap \<Rightarrow> loc list \<Rightarrow> _"
  where "valid prev next s \<longleftrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length s) \<longrightarrow> \<not>s ! nat i = null \<and> s ! nat i |\<in>| fmdom prev \<and> s ! nat i |\<in>| fmdom next \<and> (\<forall>(j :: int). i < j \<and> j < int (length s) \<longrightarrow> \<not>s ! nat i = s ! nat j))" for prev "next" s
definition dll :: "(loc, loc) fmap \<Rightarrow> (loc, loc) fmap \<Rightarrow> loc list \<Rightarrow> loc \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "dll prev next s head lo hi \<longleftrightarrow> valid prev next s \<and> ((0 :: int) \<le> lo \<and> lo \<le> hi \<and> hi \<le> int (length s)) \<and> head = (if lo = int (length s) then null else s ! nat lo) \<and> (\<forall>(i :: int). lo \<le> i \<and> i < hi - (1 :: int) \<longrightarrow> fm_contents next (s ! nat i) = s ! nat (i + (1 :: int))) \<and> (\<forall>(i :: int). lo < i \<and> i < hi \<longrightarrow> fm_contents prev (s ! nat i) = s ! nat (i - (1 :: int))) \<and> (lo < hi \<longrightarrow> fm_contents next (s ! nat (hi - (1 :: int))) = (if hi = int (length s) then null else s ! nat hi)) \<and> (lo < hi \<longrightarrow> fm_contents prev (s ! nat lo) = (if lo = (0 :: int) then null else s ! nat (lo - (1 :: int))))" for prev "next" s head lo hi
fun tree :: "(loc, loc) fmap \<Rightarrow> (loc, loc) fmap \<Rightarrow> loc list \<Rightarrow> loc \<Rightarrow> int tree \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "tree prev next s root t1 lo hi = (valid prev next s \<and> ((0 :: int) \<le> lo \<and> lo \<le> hi \<and> hi \<le> int (length s)) \<and> (case t1 of (Empty :: int tree) \<Rightarrow> root = null \<and> lo = hi | Node l p r \<Rightarrow> (lo \<le> p \<and> p < hi) \<and> root = s ! nat p \<and> tree prev next s (fm_contents prev root) l lo p \<and> tree prev next s (fm_contents next root) r (p + (1 :: int)) hi))" for prev "next" s root t1 lo hi
fun inorder :: "loc list \<Rightarrow> int tree \<Rightarrow> loc list"
  where "inorder s (Empty :: int tree) = []" for s
      | "inorder s (Node l p r) = inorder s l @ Cons (s ! nat p) (inorder s r)" for s l p r
theorem size_alt'vc:
  fixes prev :: "loc t"
  fixes "next" :: "loc t"
  fixes s :: "loc list"
  fixes head :: "loc"
  assumes fact0: "dll (to_fmap prev) (to_fmap next) s head (0 :: int) (int (length s))"
  shows "dll (to_fmap prev) (to_fmap next) s head (0 :: int) (int (length s))"
  and "\<forall>(len :: int) (p :: loc). dll (to_fmap prev) (to_fmap next) s p len (int (length s)) \<longrightarrow> (if \<not>p = null then p |\<in>| fmdom (to_fmap next) \<and> (let o1 :: loc = fm_contents (to_fmap next) p in o1 = the (fmlookup (to_fmap next) p) \<longrightarrow> ((0 :: int) \<le> int (length s) - len \<and> int (length s) - (len + (1 :: int)) < int (length s) - len) \<and> dll (to_fmap prev) (to_fmap next) s o1 (len + (1 :: int)) (int (length s))) else len = int (length s))"
  sorry
end
