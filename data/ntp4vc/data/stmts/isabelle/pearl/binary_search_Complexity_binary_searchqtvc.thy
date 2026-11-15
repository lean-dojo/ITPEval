theory binary_search_Complexity_binary_searchqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref"
begin
consts log2 :: "int \<Rightarrow> int"
axiomatization where log2'def:   "if n \<le> (1 :: int) then log2 n = (0 :: int) else log2 n = (1 :: int) + log2 (n cdiv (2 :: int))"
  for n :: "int"
definition f :: "int \<Rightarrow> int"
  where "f n = (if n = (0 :: int) then 0 :: int else (1 :: int) + log2 n)" for n
theorem binary_search'vc:
  fixes a :: "int list"
  fixes v :: "int"
  assumes fact0: "\<forall>(i1 :: int) (i2 :: int). (0 :: int) \<le> i1 \<and> i1 \<le> i2 \<and> i2 < int (length a) \<longrightarrow> a ! nat i1 \<le> a ! nat i2"
  shows "let o1 :: int = int (length a) in (((0 :: int) \<le> (0 :: int) \<and> (0 :: int) \<le> o1 \<and> o1 \<le> int (length a)) \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < (0 :: int) \<or> o1 \<le> i \<and> i < int (length a) \<longrightarrow> \<not>a ! nat i = v) \<and> (0 :: int) - (0 :: int) + f (o1 - (0 :: int)) \<le> f (int (length a))) \<and> (\<forall>(hi :: int) (lo :: int) (time :: int). ((0 :: int) \<le> lo \<and> lo \<le> hi \<and> hi \<le> int (length a)) \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < lo \<or> hi \<le> i \<and> i < int (length a) \<longrightarrow> \<not>a ! nat i = v) \<and> time - (0 :: int) + f (hi - lo) \<le> f (int (length a)) \<longrightarrow> (if lo < hi then \<not>(2 :: int) = (0 :: int) \<and> (let mid :: int = lo + (hi - lo) cdiv (2 :: int) in ((0 :: int) \<le> mid \<and> mid < int (length a)) \<and> (if a ! nat mid < v then ((0 :: int) \<le> hi - lo \<and> hi - (mid + (1 :: int)) < hi - lo) \<and> ((0 :: int) \<le> mid + (1 :: int) \<and> mid + (1 :: int) \<le> hi \<and> hi \<le> int (length a)) \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < mid + (1 :: int) \<or> hi \<le> i \<and> i < int (length a) \<longrightarrow> \<not>a ! nat i = v) \<and> time + (1 :: int) - (0 :: int) + f (hi - (mid + (1 :: int))) \<le> f (int (length a)) else ((0 :: int) \<le> mid \<and> mid < int (length a)) \<and> (if v < a ! nat mid then ((0 :: int) \<le> hi - lo \<and> mid - lo < hi - lo) \<and> ((0 :: int) \<le> lo \<and> lo \<le> mid \<and> mid \<le> int (length a)) \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < lo \<or> mid \<le> i \<and> i < int (length a) \<longrightarrow> \<not>a ! nat i = v) \<and> time + (1 :: int) - (0 :: int) + f (mid - lo) \<le> f (int (length a)) else (((0 :: int) \<le> mid \<and> mid < int (length a)) \<and> a ! nat mid = v \<or> mid = -(1 :: int) \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length a) \<longrightarrow> \<not>a ! nat i = v)) \<and> time - (0 :: int) \<le> f (int (length a))))) else (((0 :: int) \<le> -(1 :: int) \<and> -(1 :: int) < int (length a)) \<and> a ! nat (-(1 :: int)) = v \<or> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length a) \<longrightarrow> \<not>a ! nat i = v)) \<and> time - (0 :: int) \<le> f (int (length a))))"
  sorry
end
