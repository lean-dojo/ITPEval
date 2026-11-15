theory there_and_back_again_Palindrome_palindromeqtvc
  imports "NTP4Verif.NTP4Verif"
begin
definition pal :: "'a list \<Rightarrow> int \<Rightarrow> _"
  where "pal x n \<longleftrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < n \<longrightarrow> nth_opt x i = nth_opt x (n - (1 :: int) - i))" for x n
typedecl  elt
consts eq :: "elt \<Rightarrow> elt \<Rightarrow> bool"
axiomatization where eq'spec:   "eq x y \<longleftrightarrow> x = y"
  for x :: "elt"
  and y :: "elt"
theorem palindrome'vc:
  fixes x :: "elt list"
  shows "length x \<le> length x"
  and "\<forall>(o1 :: elt list). (\<exists>(x0 :: elt list). length x0 = length x \<and> x = x0 @ o1) \<and> pal x (int (length x)) \<longrightarrow> pal x (int (length x))"
  and "(\<exists>(i :: int). ((0 :: int) \<le> i \<and> i < int (length x)) \<and> \<not>nth_opt x i = nth_opt x (int (length x) - (1 :: int) - i)) \<longrightarrow> \<not>pal x (int (length x))"
  sorry
end
