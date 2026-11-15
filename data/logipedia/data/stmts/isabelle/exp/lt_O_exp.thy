(*
  Statement-only formalization of Logipedia corpus artifact exp.lt_O_exp,
  catalog title "exp.lt_O_exp": every positive natural base has a positive
  natural power at every natural exponent. This file contains no proof.
*)

theory lt_O_exp
  imports Main
begin

theorem lt_O_exp:
  "\<forall>n m :: nat. 0 < n \<longrightarrow> 0 < n ^ m"
  sorry

end
