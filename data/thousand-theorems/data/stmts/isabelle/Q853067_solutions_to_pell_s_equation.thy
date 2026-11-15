(*
  Statement-only formalization of thousand-theorems corpus artifact Q853067
  (thousand-theorems__isabelle__Q853067), "Solutions to Pell's equation":
  every natural-number solution for coefficient a squared minus one occurs
  in the recursively defined Pell sequence. This file contains no proof.
*)

theory Q853067_solutions_to_pell_s_equation
  imports Main
begin

fun q853067_pell :: "nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat" where
  "q853067_pell a 0 = (1, 0)"
| "q853067_pell a (Suc n) =
    (fst (q853067_pell a n) * a +
       (a * a - 1) * snd (q853067_pell a n),
     fst (q853067_pell a n) +
       snd (q853067_pell a n) * a)"

definition q853067_xn :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "q853067_xn a n = fst (q853067_pell a n)"

definition q853067_yn :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "q853067_yn a n = snd (q853067_pell a n)"

theorem q853067_eq_pell:
  fixes a x y :: nat
  assumes "1 < a"
    and "x * x - (a * a - 1) * y * y = 1"
  shows "\<exists>n::nat. x = q853067_xn a n \<and> y = q853067_yn a n"
  sorry

end
