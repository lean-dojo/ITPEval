(*
  Statement-only formalization of Logipedia corpus artifact nat.times_Sn_m,
  catalog title "nat.times_Sn_m": multiplying the successor of a natural
  number by another natural number equals that number plus the preceding
  product. This file contains no proof.
*)

theory times_Sn_m
  imports Main
begin

theorem times_Sn_m:
  "\<forall>n m :: nat. m + n * m = Suc n * m"
  sorry

end
