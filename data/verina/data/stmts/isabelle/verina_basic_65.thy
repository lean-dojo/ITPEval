(*
  Statement-only formalization of VERINA corpus artifact verina_basic_65
  (verina__isabelle__verina_basic_65), catalog title "SquareRoot": an
  executable bounded recursion computes the integer square root of a natural
  number, together with its unconditional precondition, exact square-bound
  postcondition, and final correctness proposition. This file contains no
  proof.
*)

theory verina_basic_65
  imports Main
begin

definition SquareRoot_precond :: "nat \<Rightarrow> bool" where
  "SquareRoot_precond N \<longleftrightarrow> True"

fun SquareRoot_boundedLoop ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "SquareRoot_boundedLoop N 0 r = r"
| "SquareRoot_boundedLoop N (Suc bound) r =
    (if (r + 1) * (r + 1) \<le> N
     then SquareRoot_boundedLoop N bound (r + 1)
     else r)"

definition SquareRoot :: "nat \<Rightarrow> nat" where
  "SquareRoot N = SquareRoot_boundedLoop N (N + 1) 0"

definition SquareRoot_postcond :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "SquareRoot_postcond N result \<longleftrightarrow>
    result * result \<le> N \<and>
    N < (result + 1) * (result + 1)"

theorem SquareRoot_spec_satisfied:
  fixes N :: nat
  assumes "SquareRoot_precond N"
  shows "SquareRoot_postcond N (SquareRoot N)"
  sorry

end
