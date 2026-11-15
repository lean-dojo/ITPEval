(*
  Authors: Wenda Li
*)

theory amc12_2000_p6
  imports Complex_Main "HOL-Number_Theory.Number_Theory"
begin

theorem amc12_2000_p6:
  fixes p q ::nat
  assumes h0: "prime p \<and> prime q"
    and h1: "4 \<le> p \<and> p \<le> 18"
    and h2: "4 \<le> q \<and> q \<le> 18" 
  shows "((p *  q)::int) - (p + q) \<noteq> 194"
  by sorry

end

