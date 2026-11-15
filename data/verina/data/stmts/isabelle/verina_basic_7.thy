(*
  Statement-only formalization of VERINA corpus artifact verina_basic_7
  (verina__isabelle__verina_basic_7), catalog title
  "sumOfSquaresOfFirstNOddNumbers": an executable natural-number recursion
  sums the squares of the first n odd numbers, together with its unconditional
  precondition, closed-form postcondition, and final correctness proposition.
  This file contains no proof.
*)

theory verina_basic_7
  imports Main
begin

definition sumOfSquaresOfFirstNOddNumbers_precond ::
    "nat \<Rightarrow> bool" where
  "sumOfSquaresOfFirstNOddNumbers_precond n \<longleftrightarrow> True"

fun sumOfSquaresOfFirstNOddNumbers_loop ::
    "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "sumOfSquaresOfFirstNOddNumbers_loop 0 acc = acc"
| "sumOfSquaresOfFirstNOddNumbers_loop (Suc k) acc =
    sumOfSquaresOfFirstNOddNumbers_loop k
      (acc + (2 * (Suc k) - 1) * (2 * (Suc k) - 1))"

definition sumOfSquaresOfFirstNOddNumbers :: "nat \<Rightarrow> nat" where
  "sumOfSquaresOfFirstNOddNumbers n =
    sumOfSquaresOfFirstNOddNumbers_loop n 0"

definition sumOfSquaresOfFirstNOddNumbers_postcond ::
    "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "sumOfSquaresOfFirstNOddNumbers_postcond n result \<longleftrightarrow>
    result - (n * (2 * n - 1) * (2 * n + 1)) div 3 = 0 \<and>
    (n * (2 * n - 1) * (2 * n + 1)) div 3 - result = 0"

theorem sumOfSquaresOfFirstNOddNumbers_spec_satisfied:
  assumes "sumOfSquaresOfFirstNOddNumbers_precond n"
  shows
    "sumOfSquaresOfFirstNOddNumbers_postcond
      n (sumOfSquaresOfFirstNOddNumbers n)"
  sorry

end
