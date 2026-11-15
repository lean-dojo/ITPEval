(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2024_a2
  (putnambench__isabelle__putnam_2024_a2): the real polynomials p for which
  p(p(x)) - x is (p(x) - x)^2 times a real polynomial are exactly the affine
  polynomials with slope 1 or -1. This file contains no proof.
*)

theory putnam_2024_a2
  imports Complex_Main
begin

definition putnam_2024_a2_is_poly :: "(nat \<Rightarrow> real) \<Rightarrow> bool" where
  "putnam_2024_a2_is_poly p \<longleftrightarrow> finite {n. p n \<noteq> 0}"

definition putnam_2024_a2_eval :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real" where
  "putnam_2024_a2_eval p x = (\<Sum>n\<in>{n. p n \<noteq> 0}. p n * x ^ n)"

definition putnam_2024_a2_solution :: "(nat \<Rightarrow> real) set" where
  "putnam_2024_a2_solution =
    {p. \<exists>a :: real.
      p = (\<lambda>n. if n = 0 then a else if n = 1 then 1 else 0) \<or>
      p = (\<lambda>n. if n = 0 then a else if n = 1 then -1 else 0)}"

theorem putnam_2024_a2:
  shows
    "{p :: nat \<Rightarrow> real.
      putnam_2024_a2_is_poly p \<and>
      (\<exists>q :: nat \<Rightarrow> real.
        putnam_2024_a2_is_poly q \<and>
        (\<forall>x :: real.
          putnam_2024_a2_eval p (putnam_2024_a2_eval p x) - x =
            (putnam_2024_a2_eval p x - x) ^ 2 *
              putnam_2024_a2_eval q x))}
      = putnam_2024_a2_solution"
  sorry

end
