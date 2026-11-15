(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2025_b6
  (putnambench__isabelle__putnam_2025_b6): the greatest real exponent for
  which a positive-integer-valued function can satisfy the stated iterated
  growth inequality is 1 / 4. This file contains no proof.
*)

theory putnam_2025_b6
  imports Complex_Main
begin

definition putnam_2025_b6_admissible :: "real \<Rightarrow> bool" where
  "putnam_2025_b6_admissible r \<longleftrightarrow>
    (\<exists>g :: nat \<Rightarrow> nat.
      (\<forall>n :: nat. 0 < n \<longrightarrow> 0 < g n) \<and>
      (\<forall>n :: nat. 0 < n \<longrightarrow>
        real (g (g n)) powr r
          \<le> real (g (n + 1)) - real (g n)))"

definition putnam_2025_b6_solution :: real where
  "putnam_2025_b6_solution = 1 / 4"

theorem putnam_2025_b6:
  shows
    "putnam_2025_b6_admissible putnam_2025_b6_solution \<and>
      (\<forall>r :: real.
        putnam_2025_b6_admissible r
          \<longrightarrow> r \<le> putnam_2025_b6_solution)"
  sorry

end
