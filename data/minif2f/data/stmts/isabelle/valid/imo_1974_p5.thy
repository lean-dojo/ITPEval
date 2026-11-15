(*
  Authors: Albert Qiaochu Jiang
*)

theory imo_1974_p5 imports
  Complex_Main
begin

theorem imo_1974_p5:

  fixes a b c d s :: real
  assumes h0 : "0 < a \<and> 0 < b \<and> 0 < c \<and> 0 < d"
    and h1 : "s=a/(a+b+d) + b/(a+b+c) + c/(b+c+d) + d/(a+c+d)"
  shows "1<s \<and> s<2"
  by sorry

end
