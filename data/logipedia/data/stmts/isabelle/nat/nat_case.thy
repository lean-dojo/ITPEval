(*
  Statement-only formalization of Logipedia corpus artifact nat.nat_case,
  catalog title nat.nat_case: a predicate holds for a natural number when it
  holds in the equality-guarded zero and successor cases. This file contains
  no proof.
*)

theory nat_case
  imports Main
begin

theorem nat_case:
  "\<forall>n :: nat. \<forall>P :: nat \<Rightarrow> bool.
    (n = 0 \<longrightarrow> P 0) \<longrightarrow>
    (\<forall>m :: nat. n = Suc m \<longrightarrow> P (Suc m)) \<longrightarrow>
    P n"
  sorry

end
