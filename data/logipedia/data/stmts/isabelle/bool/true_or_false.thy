(*
  Statement-only formalization of Logipedia corpus artifact
  bool.true_or_false, catalog title bool.true_or_false: every Boolean value is
  equal to true or equal to false. This file contains no proof.
*)

theory true_or_false
  imports Main
begin

theorem true_or_false:
  "\<forall>b::bool. b = True \<or> b = False"
  sorry

end
