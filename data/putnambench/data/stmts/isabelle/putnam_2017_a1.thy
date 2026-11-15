theory putnam_2017_a1 imports Complex_Main
begin

definition putnam_2017_a1_solution :: "int set" where
  "putnam_2017_a1_solution \<equiv>
    {x :: int. x > 0 \<and> (x = 1 \<or> 5 dvd x)}"
(* { x::int . x > 0 \<and> (x = 1 \<or> 5 dvd x) } *)
theorem putnam_2017_a1:
  fixes IsQualifying :: "(int set) \<Rightarrow> bool"
    and S :: "int set"
  assumes IsQualifying_def : "\<forall>S. IsQualifying S \<longleftrightarrow>
    (\<forall> n \<in> S. 0 < n) \<and>
    2 \<in> S \<and>
    (\<forall> n > 0. n^2 \<in> S \<longrightarrow> n \<in> S) \<and>
    (\<forall> n \<in> S. (n + 5)^2 \<in> S)"
    and hS : "IsQualifying S \<and> (\<forall>A. IsQualifying A \<longrightarrow> S \<subseteq> A)"
  shows "{x :: int. x > 0} - S = putnam_2017_a1_solution"
  sorry

end
