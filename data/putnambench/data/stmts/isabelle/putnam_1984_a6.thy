theory putnam_1984_a6 imports Complex_Main
"HOL-Number_Theory.Cong"
begin

definition putnam_1984_a6_solution :: "nat" where
"putnam_1984_a6_solution \<equiv> 4"
theorem putnam_1984_a6:
  fixes f :: "nat \<Rightarrow> nat"
    and IsPeriodicFrom :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> bool"
    and P :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> bool"
  assumes hf : "\<forall> n > 0. f n =
      (THE d :: nat. \<exists> m t :: nat.
        fact n = 10^t * m \<and> d = m mod 10 \<and> d \<noteq> 0)"
    and P_def : "\<forall> x g p. P x g p \<longleftrightarrow>
      (if p = 0 then
        (\<forall> q > 0. \<not> IsPeriodicFrom x g q)
       else
        0 < p \<and> IsPeriodicFrom x g p \<and>
          (\<forall> q > 0. IsPeriodicFrom x g q \<longrightarrow> p \<le> q))"
    and IsPeriodicFrom_def : "\<forall> x f p. (IsPeriodicFrom x f p \<longleftrightarrow> (\<forall> (s :: nat) \<ge> x. f s = f (s + p)))"
  shows "\<exists> g :: nat \<Rightarrow> nat.
    (\<forall> (k :: nat) (a :: nat \<Rightarrow> nat).
      (k > 0 \<and> inj_on a {0..<k}) \<longrightarrow>
      f (\<Sum> i \<in> {0..<k}. 5^(a i)) = g (\<Sum> i \<in> {0..<k}. a i))
    \<and> P 1 g putnam_1984_a6_solution"
  sorry

end
