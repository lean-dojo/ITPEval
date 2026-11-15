(*
  Statement-only formalization of Logipedia corpus artifact nat.transitive_lt,
  catalog title "nat.transitive_lt": the strict less-than relation on natural
  numbers is transitive. This file contains no proof.
*)

theory transitive_lt
  imports Main
begin

theorem transitive_lt:
  "\<forall>a b c :: nat.
    a < b \<longrightarrow> b < c \<longrightarrow> a < c"
  sorry

end
