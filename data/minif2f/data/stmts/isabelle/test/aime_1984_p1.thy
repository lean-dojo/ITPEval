(*
  Authors: Wenda Li
*)

theory aime_1984_p1 imports Complex_Main
begin

theorem aime_1984_p1:
  fixes u :: "nat \<Rightarrow> rat"
  assumes h0: "\<forall> n. u (n + 1) = u n + 1"
    and h1: "(\<Sum> k < 98. u (k+1)) = 137" 
  shows "(\<Sum> k < 49. u (2 * (k+1))) = 93"
  by sorry

end