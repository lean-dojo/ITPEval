(*
  Statement-only formalization of VERINA corpus artifact verina_basic_53
  (verina__isabelle__verina_basic_53), catalog title "CalSum": an executable
  natural-number recursion sums from N down to zero and satisfies the
  triangular-number identity, together with its unconditional precondition,
  postcondition, and final correctness proposition. This file contains no
  proof.
*)

theory verina_basic_53
  imports Main
begin

definition CalSum_precond :: "nat \<Rightarrow> bool" where
  "CalSum_precond N \<longleftrightarrow> True"

fun CalSum_loop :: "nat \<Rightarrow> nat" where
  "CalSum_loop 0 = 0"
| "CalSum_loop (Suc n) = Suc n + CalSum_loop n"

definition CalSum :: "nat \<Rightarrow> nat" where
  "CalSum N = CalSum_loop N"

definition CalSum_postcond :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "CalSum_postcond N result \<longleftrightarrow>
    2 * result = N * (N + 1)"

theorem CalSum_spec_satisfied:
  assumes "CalSum_precond N"
  shows "CalSum_postcond N (CalSum N)"
  sorry

end
