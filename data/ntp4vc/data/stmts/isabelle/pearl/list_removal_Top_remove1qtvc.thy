theory list_removal_Top_remove1qtvc
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
theorem remove1'vc:
  fixes n1 :: "int"
  fixes n2 :: "int"
  fixes mem1 :: "loc \<Rightarrow> loc"
  assumes fact0: "(0 :: int) < n1"
  assumes fact1: "(0 :: int) < n2"
  assumes fact2: "list mem1 head n1 entry"
  assumes fact3: "list mem1 entry n2 null"
  shows "let o1 :: loc = head in \<not>o1 = null \<and> (let o2 :: loc = mem1 o1 in (((0 :: int) < (1 :: int) \<and> (1 :: int) \<le> n1) \<and> list mem1 head (1 :: int) o2 \<and> \<not>o2 = null \<and> list mem1 o2 (n1 - (1 :: int)) entry \<and> list mem1 entry n2 null) \<and> (\<forall>(n :: int) (curr :: loc) (prev :: loc). ((0 :: int) < n \<and> n \<le> n1) \<and> list mem1 head n curr \<and> \<not>curr = null \<and> (prev = null \<longrightarrow> n = (1 :: int)) \<and> (\<not>prev = null \<longrightarrow> mem1 prev = curr) \<and> (\<not>prev = null \<longrightarrow> list mem1 head (n - (1 :: int)) prev) \<and> list mem1 curr (n1 - n) entry \<and> list mem1 entry n2 null \<longrightarrow> (if \<not>curr = entry then \<not>curr = null \<and> ((0 :: int) \<le> n1 - n \<and> n1 - (n + (1 :: int)) < n1 - n) \<and> ((0 :: int) < n + (1 :: int) \<and> n + (1 :: int) \<le> n1) \<and> list mem1 head (n + (1 :: int)) (mem1 curr) \<and> \<not>mem1 curr = null \<and> (curr = null \<longrightarrow> n + (1 :: int) = (1 :: int)) \<and> (\<not>curr = null \<longrightarrow> True) \<and> (\<not>curr = null \<longrightarrow> list mem1 head (n + (1 :: int) - (1 :: int)) curr) \<and> list mem1 (mem1 curr) (n1 - (n + (1 :: int))) entry \<and> list mem1 entry n2 null else if prev = null then \<not>curr = null \<and> (let o3 :: loc = head in \<not>o3 = null \<and> list (mem1(o3 := mem1 curr)) head (n1 + n2 - (1 :: int)) null) else \<not>curr = null \<and> \<not>prev = null \<and> list (mem1(prev := mem1 curr)) head (n1 + n2 - (1 :: int)) null)))"
  sorry
end
