(*
  Statement-only formalization of Logipedia corpus artifact nat.nat_elim2,
  catalog title "nat.nat_elim2": two-dimensional induction on pairs of
  natural numbers from the zero row, the positive zero column, and a
  simultaneous-successor step. This file contains no proof.
*)

theory nat_elim2
  imports Main
begin

theorem nat_elim2:
  "\<forall>R :: nat \<Rightarrow> nat \<Rightarrow> bool.
    (\<forall>n :: nat. R 0 n) \<longrightarrow>
    (\<forall>n :: nat. R (Suc n) 0) \<longrightarrow>
    (\<forall>n m :: nat. R n m \<longrightarrow> R (Suc n) (Suc m)) \<longrightarrow>
    (\<forall>n m :: nat. R n m)"
  sorry

end
