theory sf_HoareLogic_factorialqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref"
begin
inductive even :: "int \<Rightarrow> bool" where
   even_0: "even (0 :: int)"
 | even_odd: "even x \<Longrightarrow> even (x + (2 :: int))" for x :: "int"
consts fact :: "int \<Rightarrow> int"
axiomatization where fact_0:   "fact (0 :: int) = (1 :: int)"
axiomatization where fact_n:   "fact n = n * fact (n - (1 :: int))"
 if "(0 :: int) < n"
  for n :: "int"
theorem factorial'vc:
  fixes x :: "int"
  assumes fact0: "(0 :: int) \<le> x"
  shows "(0 :: int) \<le> x"
  and "(1 :: int) * fact x = fact x"
  and "\<forall>(z :: int) (y :: int). (0 :: int) \<le> z \<and> y * fact z = fact x \<longrightarrow> (if \<not>z = (0 :: int) then ((0 :: int) \<le> z \<and> z - (1 :: int) < z) \<and> (0 :: int) \<le> z - (1 :: int) \<and> y * z * fact (z - (1 :: int)) = fact x else y = fact x)"
  sorry
end
