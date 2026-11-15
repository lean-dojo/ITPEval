(*
  Statement-only formalization of Logipedia corpus artifact nat.leb_elim,
  catalog title "nat.leb_elim": elimination for recursively computed
  natural-number Boolean less-than-or-equal comparison by the at-most and
  not-at-most cases. This file contains no proof.
*)

theory leb_elim
  imports Main
begin

fun leb :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "leb 0 m = True"
| "leb (Suc n) 0 = False"
| "leb (Suc n) (Suc m) = leb n m"

theorem leb_elim:
  "\<forall>n m :: nat.
    \<forall>P :: bool \<Rightarrow> bool.
      (n \<le> m \<longrightarrow> P True) \<longrightarrow>
      (\<not> (n \<le> m) \<longrightarrow> P False) \<longrightarrow>
      P (leb n m)"
  sorry

end
