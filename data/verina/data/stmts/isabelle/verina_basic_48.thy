(*
  Statement-only formalization of VERINA corpus artifact verina_basic_48
  (verina__isabelle__verina_basic_48), catalog title "isPerfectSquare": an
  executable fuel-bounded natural-number search decides whether its input has
  a natural square root, together with its unconditional precondition,
  biconditional postcondition, and final correctness proposition. This file
  contains no proof.
*)

theory verina_basic_48
  imports Main
begin

definition isPerfectSquare_precond :: "nat \<Rightarrow> bool" where
  "isPerfectSquare_precond n \<longleftrightarrow> True"

fun isPerfectSquare_check ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "isPerfectSquare_check n x 0 = False"
| "isPerfectSquare_check n x (Suc fuel) =
    (if x * x > n
     then False
     else if x * x = n
          then True
          else isPerfectSquare_check n (x + 1) fuel)"

definition isPerfectSquare :: "nat \<Rightarrow> bool" where
  "isPerfectSquare n =
    (if n = 0 then True else isPerfectSquare_check n 1 n)"

definition isPerfectSquare_postcond :: "nat \<Rightarrow> bool \<Rightarrow> bool" where
  "isPerfectSquare_postcond n result \<longleftrightarrow>
    (result \<longleftrightarrow> (\<exists>i :: nat. i * i = n))"

theorem isPerfectSquare_spec_satisfied:
  fixes n :: nat
  assumes "isPerfectSquare_precond n"
  shows "isPerfectSquare_postcond n (isPerfectSquare n)"
  sorry

end
