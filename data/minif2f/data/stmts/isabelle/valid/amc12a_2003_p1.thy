(*
  Authors: Wenda Li
*)

theory amc12a_2003_p1 imports
  Complex_Main
begin

theorem amc12a_2003_p1:
  fixes u v :: "nat \<Rightarrow> nat"
  assumes u:"\<forall>n. u n = 2 *n +2"
      and v:"\<forall>n. v n= 2* n +1"
    shows "(\<Sum> k < 2003. u k) - (\<Sum> k < 2003. v k) = 2003"
      (is "?L = ?R")
  by sorry

end
