(*
  Authors: Wenda Li
*)

theory imo_1982_p1 imports 
  Complex_Main 
  "HOL-Computational_Algebra.Computational_Algebra"
begin

theorem imo_1982_p1:
  fixes f :: "nat \<Rightarrow> nat"
  assumes "\<forall> m n. 0 < m \<longrightarrow> 0 < n \<longrightarrow>
    (f (m + n) = f m + f n \<or> f (m + n) = f m + f n + 1)"
    and "f 2 = 0"
    and "0 < f 3"
    and "f 9999 = 3333" 
  shows "f 1982 = 660"
  by sorry

end
