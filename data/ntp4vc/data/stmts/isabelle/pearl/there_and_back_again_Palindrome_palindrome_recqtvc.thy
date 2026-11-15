theory there_and_back_again_Palindrome_palindrome_recqtvc
  imports "NTP4Verif.NTP4Verif"
begin
definition pal :: "'a list \<Rightarrow> int \<Rightarrow> _"
  where "pal x n \<longleftrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < n \<longrightarrow> nth_opt x i = nth_opt x (n - (1 :: int) - i))" for x n
typedecl  elt
consts eq :: "elt \<Rightarrow> elt \<Rightarrow> bool"
axiomatization where eq'spec:   "eq x y \<longleftrightarrow> x = y"
  for x :: "elt"
  and y :: "elt"
theorem palindrome_rec'vc:
  fixes y :: "elt list"
  fixes x :: "elt list"
  assumes fact0: "length y \<le> length x"
  shows "case y of Nil \<Rightarrow> (\<exists>(x0 :: elt list). length x0 = length y \<and> x = x0 @ x) \<and> pal x (int (length y)) | Cons x1 x2 \<Rightarrow> (case x2 of Nil \<Rightarrow> (case x of Cons x3 x4 \<Rightarrow> (\<exists>(x0 :: elt list). length x0 = length y \<and> x = x0 @ x4) \<and> pal x (int (length y)) | _ \<Rightarrow> False) | Cons x3 x4 \<Rightarrow> (case x of Cons x5 x6 \<Rightarrow> ((case x of Nil \<Rightarrow> False | Cons _ f \<Rightarrow> f = x6) \<and> length x4 \<le> length x6) \<and> (\<forall>(o1 :: elt list). (\<exists>(x0 :: elt list). length x0 = length x4 \<and> x6 = x0 @ o1) \<and> pal x6 (int (length x4)) \<longrightarrow> (case o1 of Cons x11 xs \<Rightarrow> (eq x5 x11 \<longleftrightarrow> x5 = x11) \<longrightarrow> (if eq x5 x11 then (\<exists>(x0 :: elt list). length x0 = length y \<and> x = x0 @ xs) \<and> pal x (int (length y)) else \<exists>(i :: int). ((0 :: int) \<le> i \<and> i < int (length y)) \<and> \<not>nth_opt x i = nth_opt x (int (length y) - (1 :: int) - i)) | Nil \<Rightarrow> False)) \<and> ((\<exists>(i :: int). ((0 :: int) \<le> i \<and> i < int (length x4)) \<and> \<not>nth_opt x6 i = nth_opt x6 (int (length x4) - (1 :: int) - i)) \<longrightarrow> (\<exists>(i :: int). ((0 :: int) \<le> i \<and> i < int (length y)) \<and> \<not>nth_opt x i = nth_opt x (int (length y) - (1 :: int) - i))) | _ \<Rightarrow> False))"
  sorry
end
