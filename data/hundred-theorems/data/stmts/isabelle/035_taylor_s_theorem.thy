(*
  Statement-only formalization of Taylor's theorem from Hundred Theorems
  item 035. The remainder is in Lagrange form at a point strictly between the
  expansion point and the evaluation point. This file contains no proof.
*)

theory Taylor_Theorem
  imports Complex_Main
begin

theorem hundred_theorems_taylor:
  fixes c x :: real and n :: nat
  assumes init: "n > 0" "diff 0 = f"
    and derivatives:
      "\<forall>m t. m < n \<and> min c x \<le> t \<and> t \<le> max c x
        \<longrightarrow> DERIV (diff m) t :> diff (Suc m) t"
    and distinct: "x \<noteq> c"
  shows "\<exists>t.
    (if x < c then x < t \<and> t < c else c < t \<and> t < x) \<and>
    f x = (\<Sum>m<n. (diff m c / fact m) * (x - c)^m)
      + (diff n t / fact n) * (x - c)^n"
  sorry

end
