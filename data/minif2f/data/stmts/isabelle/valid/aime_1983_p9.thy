(*
  Authors: Wenda Li
*)

theory aime_1983_p9 imports
  Complex_Main
begin

theorem aime_1983_p9:
  fixes x::real
  assumes "0<x" "x<pi"
  shows "12 \<le> ((9 * (x^2 * (sin x)^2)) + 4) / (x * sin x)"
  by sorry

end