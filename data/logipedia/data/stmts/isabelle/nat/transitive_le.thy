(*
  Statement-only formalization of Logipedia corpus artifact nat.transitive_le,
  catalog title "nat.transitive_le": the less-than-or-equal relation on natural
  numbers is transitive. This file contains no proof.
*)

theory transitive_le
  imports Main
begin

theorem transitive_le:
  "\<forall>a b c :: nat.
    a \<le> b \<longrightarrow> b \<le> c \<longrightarrow> a \<le> c"
  sorry

end
