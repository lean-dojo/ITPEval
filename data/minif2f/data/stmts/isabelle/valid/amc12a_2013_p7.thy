(*
  Authors: Albert Qiaochu Jiang
*)

theory amc12a_2013_p7 imports
  Complex_Main
begin

theorem amc12a_2013_p7:
  fixes s :: "nat \<Rightarrow> real"
  assumes h0 : "\<And>n. s (n+2) = s (n+1) + s n"
    and h1 : "s 9 = 110"
    and h2 : "s 7 = 42"
  shows "s 4 = 10"
  by sorry

end