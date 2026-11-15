(*
  Authors: Wenda Li
*)

theory amc12b_2020_p21
  imports Complex_Main 
begin

theorem amc12b_2020_p21:
  shows "card {n :: nat. 0 < n \<and>
    ((of_nat n :: real) + 1000) / 70 =
      of_int (floor (sqrt (of_nat n :: real)))} = 6"
  by sorry

end
