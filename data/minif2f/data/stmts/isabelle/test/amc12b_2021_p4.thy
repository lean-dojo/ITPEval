(*
  Authors: Wenda Li
*)

theory amc12b_2021_p4
  imports Complex_Main
begin

theorem amc12b_2021_p4:
  fixes m a :: nat
  assumes h0: "0 < m \<and> 0 < a"
    and h1: "(of_nat m :: real) / of_nat a = 3 / 4"
  shows "(84 * of_nat m + 70 * of_nat a) /
    (of_nat m + of_nat a) = (76::real)"
  by sorry

end
