(*
  Statement-only formalization of Logipedia corpus artifact
  bool.not_eq_true_false, catalog title bool.not_eq_true_false: the Boolean
  constants true and false are unequal. This file contains no proof.
*)

theory not_eq_true_false
  imports Main
begin

theorem not_eq_true_false:
  "\<not> (True = False)"
  sorry

end
