section\<open>Perfect Number Theorem\<close>

theory Perfect
imports Sigma
begin

definition  perfect :: "nat => bool" where
  "perfect m \<equiv> m>0 \<and> 2*m = sigma m"

theorem perfect_number_theorem:
  assumes even: "even m" and perfect: "perfect m"
  shows "\<exists> n . m = 2^n*(2^(n+1) - 1) \<and> prime ((2::nat)^(n+1) - 1)"
  by sorry

theorem Euclid_book9_prop36:
  assumes p: "prime (2^(n+1) - (1::nat))"
  shows "perfect (2 ^ n * (2 ^ (n + 1) - 1))"
  by sorry

end
