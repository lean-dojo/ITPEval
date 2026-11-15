theory putnam_1992_b4 imports Complex_Main
"HOL-Computational_Algebra.Polynomial"
"HOL-Analysis.Derivative"
begin

definition putnam_1992_b4_solution :: nat where
  "putnam_1992_b4_solution \<equiv> 3984"
(* 3984 *)
theorem putnam_1992_b4:
  fixes valid :: "(real poly) \<Rightarrow> bool"
  and pair :: "(real poly) \<Rightarrow> (real poly) \<Rightarrow> bool"
  and min :: nat
  defines "valid \<equiv> (\<lambda>p::real poly. p \<noteq> 0 \<and> degree p < 1992 \<and> coprime p (monom 1 3 - monom 1 1))"
  and "pair \<equiv> (\<lambda>p f::real poly. \<exists>g::real poly. g \<noteq> 0 \<and>
    (\<forall>x::real. x \<noteq> -1 \<longrightarrow> x \<noteq> 0 \<longrightarrow> x \<noteq> 1 \<longrightarrow> poly g x \<noteq> 0 \<longrightarrow>
      (deriv^^1992) (\<lambda>y::real. poly p y / (y^3 - y)) x = poly f x / poly g x))"
  and "min \<equiv> LEAST fdeg::nat. (\<exists>p f::real poly. valid p \<and> pair p f \<and> fdeg = degree f)"
  shows "min = putnam_1992_b4_solution"
  sorry

end
