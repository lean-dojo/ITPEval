(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2025_a2
  (putnambench__isabelle__putnam_2025_a2): the greatest lower coefficient and
  least upper coefficient bounding sin x by multiples of x * (pi - x) on the
  closed interval from 0 to pi are 1 / pi and 4 / pi^2. This file contains no
  proof.
*)

theory putnam_2025_a2
  imports Complex_Main
begin

definition putnam_2025_a2_solution :: "real \<times> real" where
  "putnam_2025_a2_solution = (1 / pi, 4 / pi ^ 2)"

theorem putnam_2025_a2:
  fixes a b :: real
  shows
    "((a, b) = putnam_2025_a2_solution) \<longleftrightarrow>
      ((\<forall>x \<in> {0..pi}. a * x * (pi - x) \<le> sin x) \<and>
       (\<forall>a' :: real.
          (\<forall>x \<in> {0..pi}. a' * x * (pi - x) \<le> sin x)
            \<longrightarrow> a' \<le> a) \<and>
       (\<forall>x \<in> {0..pi}. sin x \<le> b * x * (pi - x)) \<and>
       (\<forall>b' :: real.
          (\<forall>x \<in> {0..pi}. sin x \<le> b' * x * (pi - x))
            \<longrightarrow> b \<le> b'))"
  sorry

end
