(*
  Authors: Wenda Li
*)

theory imo_1977_p6 imports Complex_Main
begin

theorem imo_1977_p6:
  fixes f :: "nat \<Rightarrow> nat"
  assumes "\<forall> n. 0 < n \<longrightarrow> f (f n) < f (n + 1)"
      and "\<forall> n. f n >0"
  shows "\<forall> n. 0 < n \<longrightarrow> f n = n"
  by sorry

end
