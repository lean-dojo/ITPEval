theory equality_up_to_spaces_Top_compare_up_to_spacesqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref"
begin
typedecl  char
consts space :: "char"
consts eq :: "char \<Rightarrow> char \<Rightarrow> bool"
axiomatization where eq'spec:   "eq x y = True \<longleftrightarrow> x = y"
  for x :: "char"
  and y :: "char"
typedecl  char_string
consts remove_spaces :: "char list \<Rightarrow> char list"
axiomatization where remove_spaces'def:   "if int (length s) = (0 :: int) then remove_spaces s = s else if eq (s ! (0 :: nat)) space = True then remove_spaces s = remove_spaces (drop (1 :: nat) s) else remove_spaces s = Cons (s ! (0 :: nat)) (remove_spaces (drop (1 :: nat) s))"
  for s :: "char list"
theorem compare_up_to_spaces'vc:
  fixes x :: "char list"
  fixes y :: "char list"
  shows "let n :: int = int (length x); m :: int = int (length y) in (((0 :: int) \<le> (0 :: int) \<and> (0 :: int) \<le> n) \<and> ((0 :: int) \<le> (0 :: int) \<and> (0 :: int) \<le> m) \<and> (remove_spaces x = remove_spaces y \<longleftrightarrow> remove_spaces (drop (0 :: nat) x) = remove_spaces (drop (0 :: nat) y))) \<and> (\<forall>(j :: int) (i :: int). ((0 :: int) \<le> i \<and> i \<le> n) \<and> ((0 :: int) \<le> j \<and> j \<le> m) \<and> (remove_spaces x = remove_spaces y \<longleftrightarrow> remove_spaces (drop (nat i) x) = remove_spaces (drop (nat j) y)) \<longrightarrow> (\<forall>(o1 :: bool). (if i < n then o1 = True else o1 = (if j < m then True else False)) \<longrightarrow> (if o1 = True then \<forall>(o2 :: bool). (if i < n then let o3 :: char = space; o4 :: char = x ! nat i in o2 = eq o4 o3 \<and> (o2 = True \<longleftrightarrow> o4 = o3) else o2 = False) \<longrightarrow> (if o2 = True then ((0 :: int) \<le> n - i + m - j \<and> n - (i + (1 :: int)) + m - j < n - i + m - j) \<and> ((0 :: int) \<le> i + (1 :: int) \<and> i + (1 :: int) \<le> n) \<and> ((0 :: int) \<le> j \<and> j \<le> m) \<and> (remove_spaces x = remove_spaces y \<longleftrightarrow> remove_spaces (drop (nat (i + (1 :: int))) x) = remove_spaces (drop (nat j) y)) else \<forall>(o3 :: bool). (if j < m then let o4 :: char = space; o5 :: char = y ! nat j in o3 = eq o5 o4 \<and> (o3 = True \<longleftrightarrow> o5 = o4) else o3 = False) \<longrightarrow> (if o3 = True then ((0 :: int) \<le> n - i + m - j \<and> n - i + m - (j + (1 :: int)) < n - i + m - j) \<and> ((0 :: int) \<le> i \<and> i \<le> n) \<and> ((0 :: int) \<le> j + (1 :: int) \<and> j + (1 :: int) \<le> m) \<and> (remove_spaces x = remove_spaces y \<longleftrightarrow> remove_spaces (drop (nat i) x) = remove_spaces (drop (nat (j + (1 :: int))) y)) else \<forall>(o4 :: bool). (if i = n then o4 = True else o4 = (if j = m then True else False)) \<longrightarrow> (if o4 = True then \<not>remove_spaces x = remove_spaces y else let o5 :: char = y ! nat j; o6 :: char = x ! nat i; o7 :: bool = eq o6 o5 in (o7 = True \<longleftrightarrow> o6 = o5) \<longrightarrow> (if \<not>o7 = True then \<not>remove_spaces x = remove_spaces y else ((0 :: int) \<le> n - i + m - j \<and> n - (i + (1 :: int)) + m - (j + (1 :: int)) < n - i + m - j) \<and> ((0 :: int) \<le> i + (1 :: int) \<and> i + (1 :: int) \<le> n) \<and> ((0 :: int) \<le> j + (1 :: int) \<and> j + (1 :: int) \<le> m) \<and> (remove_spaces x = remove_spaces y \<longleftrightarrow> remove_spaces (drop (nat (i + (1 :: int))) x) = remove_spaces (drop (nat (j + (1 :: int))) y)))))) else remove_spaces x = remove_spaces y)))"
  sorry
end
