(*
  Authors: Wenda Li
*)
theory amc12_2000_p11 imports Complex_Main
begin

theorem amc12_2000_p11:
  fixes a b::real
  assumes "a \<noteq> 0" "b \<noteq> 0"
      and "a * b = a - b"
    shows "a / b + b / a - a * b = 2"
  by sorry

end