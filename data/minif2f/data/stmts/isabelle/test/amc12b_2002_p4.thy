(*
  Authors: Wenda Li
*)

theory amc12b_2002_p4
  imports Complex_Main
begin

theorem amc12b_2002_p4:
  fixes n :: nat
  assumes h0 : "0 < n"
    and h1 : "snd (quotient_of (1 / 2 + 1 / 3 + 1 / 7
                        + 1 / (rat_of_nat n))) = 1"
  shows "n = 42"
  by sorry

end
