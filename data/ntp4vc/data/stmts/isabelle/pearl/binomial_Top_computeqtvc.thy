theory binomial_Top_computeqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref"
begin
consts infix_sl :: "int \<Rightarrow> int \<Rightarrow> int"
axiomatization where infix_sl'def:   "infix_sl x y = x ediv y"
 if "\<not>y = (0 :: int)"
  for y :: "int"
  and x :: "int"
consts comb :: "int \<Rightarrow> int \<Rightarrow> int"
axiomatization where comb'def:   "if k = (0 :: int) \<or> k = n then comb n k = (1 :: int) else comb n k = comb (n - (1 :: int)) k + comb (n - (1 :: int)) (k - (1 :: int))"
 if "(0 :: int) \<le> k"
 and "k \<le> n"
  for k :: "int"
  and n :: "int"
axiomatization where comb'spec:   "(1 :: int) \<le> comb n k"
 if "(0 :: int) \<le> k"
 and "k \<le> n"
  for k :: "int"
  and n :: "int"
theorem compute'vc:
  fixes k :: "int"
  fixes n :: "int"
  assumes fact0: "(0 :: int) \<le> k"
  assumes fact1: "k \<le> n"
  shows "let k1 :: int = min k (n - k) in ((1 :: int) \<le> k1 + (1 :: int) \<longrightarrow> (((1 :: int) \<le> (1 :: int) \<and> (1 :: int) \<le> k1 + (1 :: int)) \<and> (1 :: int) = comb n ((1 :: int) - (1 :: int))) \<and> (\<forall>(r :: int). (\<forall>(i :: int). ((1 :: int) \<le> i \<and> i \<le> k1) \<and> ((1 :: int) \<le> i \<and> i \<le> k1 + (1 :: int)) \<and> r = comb n (i - (1 :: int)) \<longrightarrow> \<not>i = (0 :: int) \<and> ((1 :: int) \<le> i + (1 :: int) \<and> i + (1 :: int) \<le> k1 + (1 :: int)) \<and> infix_sl (r * (n - i + (1 :: int))) i = comb n (i + (1 :: int) - (1 :: int))) \<and> (((1 :: int) \<le> k1 + (1 :: int) \<and> k1 + (1 :: int) \<le> k1 + (1 :: int)) \<and> r = comb n (k1 + (1 :: int) - (1 :: int)) \<longrightarrow> r = comb n k))) \<and> (k1 + (1 :: int) < (1 :: int) \<longrightarrow> (1 :: int) = comb n k)"
  sorry
end
