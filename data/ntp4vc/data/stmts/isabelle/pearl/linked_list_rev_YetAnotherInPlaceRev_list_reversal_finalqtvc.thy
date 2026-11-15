theory linked_list_rev_YetAnotherInPlaceRev_list_reversal_finalqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref"
begin
typedecl  loc
consts null :: "loc"
datatype  mem = mem'mk ("next": "loc \<Rightarrow> loc")
definition valid_cells :: "(int \<Rightarrow> loc) \<Rightarrow> int \<Rightarrow> _"
  where "valid_cells s n \<longleftrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < n \<longrightarrow> \<not>s i = null) \<and> (\<forall>(i :: int) (j :: int). (0 :: int) \<le> i \<and> i < n \<longrightarrow> (0 :: int) \<le> j \<and> j < n \<longrightarrow> \<not>i = j \<longrightarrow> \<not>s i = s j)" for s n
definition listLR :: "mem \<Rightarrow> (int \<Rightarrow> loc) \<Rightarrow> loc \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "listLR m s l lo hi \<longleftrightarrow> ((0 :: int) \<le> lo \<and> lo \<le> hi) \<and> (if lo = hi then l = null else l = s lo \<and> next m (s (hi - (1 :: int))) = null \<and> (\<forall>(k :: int). lo \<le> k \<and> k < hi - (1 :: int) \<longrightarrow> next m (s k) = s (k + (1 :: int))))" for m s l lo hi
definition listRL :: "mem \<Rightarrow> (int \<Rightarrow> loc) \<Rightarrow> loc \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "listRL m s l lo hi \<longleftrightarrow> ((0 :: int) \<le> lo \<and> lo \<le> hi) \<and> (if lo = hi then l = null else next m (s lo) = null \<and> l = s (hi - (1 :: int)) \<and> (\<forall>(k :: int). lo < k \<and> k < hi \<longrightarrow> next m (s k) = s (k - (1 :: int))))" for m s l lo hi
definition frame :: "mem \<Rightarrow> mem \<Rightarrow> (int \<Rightarrow> loc) \<Rightarrow> int \<Rightarrow> _"
  where "frame m1 m2 s n \<longleftrightarrow> (\<forall>(p :: loc). (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < n \<longrightarrow> \<not>p = s i) \<longrightarrow> next m1 p = next m2 p)" for m1 m2 s n
consts is_list :: "mem \<Rightarrow> loc \<Rightarrow> (int \<Rightarrow> loc) \<Rightarrow> int \<Rightarrow> bool"
consts result :: "(int \<Rightarrow> loc) \<Rightarrow> int \<Rightarrow> loc"
axiomatization where result'def:   "result s i = s (i + (1 :: int))"
  for s :: "int \<Rightarrow> loc"
  and i :: "int"
axiomatization where is_list'def:   "if n = (0 :: int) then is_list m l s n \<longleftrightarrow> l = null else is_list m l s n \<longleftrightarrow> (let q1' :: loc = s (0 :: int) in l = q1' \<and> \<not>q1' = null) \<and> is_list m (next m l) (result s) (n - (1 :: int))"
 if "(0 :: int) \<le> n"
  for n :: "int"
  and m :: "mem"
  and l :: "loc"
  and s :: "int \<Rightarrow> loc"
consts fc :: "(int \<Rightarrow> loc) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> loc"
axiomatization where fc'def:   "fc s n i = s (n - (1 :: int) - i)"
  for s :: "int \<Rightarrow> loc"
  and n :: "int"
  and i :: "int"
theorem list_reversal_final'vc:
  fixes mem1 :: "loc \<Rightarrow> loc"
  shows "let mem2 :: mem = mem'mk mem1 in \<forall>(s :: int \<Rightarrow> loc) (n :: int) (l :: loc). (0 :: int) \<le> n \<and> is_list mem2 l s n \<longrightarrow> (valid_cells s n \<and> listLR mem2 s l (0 :: int) n) \<and> (\<forall>(mem3 :: loc \<Rightarrow> loc). let mem4 :: mem = mem'mk mem3 in \<forall>(r :: loc). listRL mem4 s r (0 :: int) n \<and> frame mem4 mem2 s n \<longrightarrow> is_list mem4 r (fc s n) n \<and> frame mem4 mem2 s n)"
  sorry
end
