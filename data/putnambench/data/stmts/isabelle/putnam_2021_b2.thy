theory putnam_2021_b2 imports Complex_Main
begin

definition putnam_2021_b2_solution :: real where
  "putnam_2021_b2_solution \<equiv> 2 / 3"
(* 2/3 *)
theorem putnam_2021_b2:
  fixes S :: "(nat \<Rightarrow> real) \<Rightarrow> real"
  and asum :: "(nat \<Rightarrow> real) \<Rightarrow> bool"
  defines "S \<equiv> \<lambda>a. suminf (\<lambda>n::nat.
    (real (n + 1) / 2^(n + 1)) *
      (\<Prod>k::nat=0..n. a k) powr (1 / real (n + 1)))"
  and "asum \<equiv> \<lambda>a.
    (\<forall>k::nat. a k \<ge> 0) \<and> summable a \<and> suminf a = 1"
  shows "(\<exists>a::nat\<Rightarrow>real.
      asum a \<and> S a = putnam_2021_b2_solution) \<and>
    (\<forall>a::nat\<Rightarrow>real.
      asum a \<longrightarrow> S a \<le> putnam_2021_b2_solution)"
  sorry

end
