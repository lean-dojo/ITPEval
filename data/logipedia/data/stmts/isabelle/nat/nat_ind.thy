(*
  Statement-only formalization of Logipedia corpus artifact nat.nat_ind,
  catalog title "nat.nat_ind": the natural-number induction principle that a
  predicate holding at zero and preserved by successor holds for every natural
  number. This file contains no proof.
*)

theory nat_ind
  imports Main
begin

theorem nat_ind:
  "\<forall>Q :: nat \<Rightarrow> bool.
    Q 0 \<longrightarrow>
    (\<forall>x :: nat. Q x \<longrightarrow> Q (Suc x)) \<longrightarrow>
    (\<forall>x :: nat. Q x)"
  sorry

end
