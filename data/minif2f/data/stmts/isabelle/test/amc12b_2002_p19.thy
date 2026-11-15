(*
  Authors: Wenda Li
*)

theory amc12b_2002_p19
  imports Complex_Main
begin

theorem amc12b_2002_p19:
  fixes a b c::real
  assumes h0: "0 < a \<and> 0 < b \<and> 0 < c"
    and h1: "a * (b + c) = 152"
    and h2: "b * (c + a) = 162"
    and h3: "c * (a + b) = 170"
  shows "a * b * c = 720"
  by sorry

end