(*
  Authors: Wenda Li
*)

theory amc12a_2003_p24 imports
  Complex_Main
begin

theorem amc12a_2003_p24:
  shows "(\<exists> a b::real. 1 < b \<and> b \<le> a \<and>
      0 = ln (a / b) / ln a + ln (b / a) / ln b)
    \<and> (\<forall> y::real. (\<exists> a b::real. 1 < b \<and> b \<le> a \<and>
      y = ln (a / b) / ln a + ln (b / a) / ln b)
      \<longrightarrow> y \<le> 0)"
  by sorry

end
