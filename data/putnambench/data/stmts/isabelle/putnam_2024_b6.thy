(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2024_b6
  (putnambench__isabelle__putnam_2024_b6): the threshold real exponent for
  the left-limit asymptotics of a power series with terms
  n^a * exp (2*n) * x^(n^2) is -1/2. This file contains no proof.
*)

theory putnam_2024_b6
  imports Complex_Main
begin

definition putnam_2024_b6_solution :: real where
  "putnam_2024_b6_solution = -1 / 2"

theorem putnam_2024_b6:
  fixes F :: "real \<Rightarrow> real \<Rightarrow> real"
    and c :: real
  assumes hF:
    "\<And>a x. x \<in> {0..<1} \<Longrightarrow>
      (\<lambda>n :: nat.
        real (Suc n) powr a *
        exp (2 * real (Suc n)) *
        x ^ ((Suc n) ^ 2))
      sums F a x"
  shows
    "((\<forall>a :: real. a < c \<longrightarrow>
        filterlim
          (\<lambda>x. F a x * exp (-1 / (1 - x)))
          (nhds 0) (at_left 1)) \<and>
      (\<forall>a :: real. c < a \<longrightarrow>
        filterlim
          (\<lambda>x. F a x * exp (-1 / (1 - x)))
          at_top (at_left 1)))
      \<longleftrightarrow> c = putnam_2024_b6_solution"
  sorry

end
