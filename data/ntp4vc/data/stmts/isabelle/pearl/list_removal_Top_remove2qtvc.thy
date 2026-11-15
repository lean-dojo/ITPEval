theory list_removal_Top_remove2qtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref"
begin
typedecl  loc
typedecl  mem
consts null :: "loc"
consts head :: "loc"
consts entry :: "loc"
axiomatization where head_is_not_null:   "\<not>head = null"
axiomatization where entry_is_not_null:   "\<not>entry = null"
axiomatization where head_is_not_entry:   "\<not>head = entry"
consts list :: "(loc \<Rightarrow> loc) \<Rightarrow> loc \<Rightarrow> int \<Rightarrow> loc \<Rightarrow> bool"
axiomatization where list'def:   "if n = (0 :: int) then list mem1 x n y \<longleftrightarrow> x = y else list mem1 x n y \<longleftrightarrow> \<not>x = null \<and> list mem1 (mem1 x) (n - (1 :: int)) y"
 if "(0 :: int) \<le> n"
  for n :: "int"
  and mem1 :: "loc \<Rightarrow> loc"
  and x :: "loc"
  and y :: "loc"
theorem remove2'vc:
  fixes n1 :: "int"
  fixes n2 :: "int"
  fixes mem1 :: "loc \<Rightarrow> loc"
  assumes fact0: "(0 :: int) < n1"
  assumes fact1: "(0 :: int) < n2"
  assumes fact2: "list mem1 head n1 entry"
  assumes fact3: "list mem1 entry n2 null"
  shows "(0 :: int) < (1 :: int)"
  and "(1 :: int) \<le> n1"
  and "\<not>head = null"
  and "list mem1 head ((1 :: int) - (1 :: int)) head"
  and "list mem1 (mem1 head) (n1 - (1 :: int)) entry"
  and "list mem1 entry n2 null"
  and "\<forall>(n :: int) (ind :: loc). ((0 :: int) < n \<and> n \<le> n1) \<and> \<not>ind = null \<and> list mem1 head (n - (1 :: int)) ind \<and> list mem1 (mem1 ind) (n1 - n) entry \<and> list mem1 entry n2 null \<longrightarrow> \<not>ind = null \<and> (if \<not>mem1 ind = entry then \<not>ind = null \<and> ((0 :: int) \<le> n1 - n \<and> n1 - (n + (1 :: int)) < n1 - n) \<and> ((0 :: int) < n + (1 :: int) \<and> n + (1 :: int) \<le> n1) \<and> \<not>mem1 ind = null \<and> list mem1 head (n + (1 :: int) - (1 :: int)) (mem1 ind) \<and> list mem1 (mem1 (mem1 ind)) (n1 - (n + (1 :: int))) entry \<and> list mem1 entry n2 null else let o1 :: loc = entry in \<not>o1 = null \<and> \<not>ind = null \<and> list (mem1(ind := mem1 o1)) head (n1 + n2 - (1 :: int)) null)"
  sorry
end
