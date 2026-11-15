(*
  Statement-only formalization of "Fermat's Last Theorem" from Hundred Theorems item 033. This
  file contains no proof.
*)

theory Fermats_Last_Theorem
  imports Main
begin

theorem fermats_last_theorem:
  fixes n :: nat
  assumes "n > 2"
  shows "\<not> (\<exists>a b c :: nat.
    a > 0 \<and> b > 0 \<and> c > 0 \<and>
    a ^ n + b ^ n = c ^ n)"
  sorry

end
