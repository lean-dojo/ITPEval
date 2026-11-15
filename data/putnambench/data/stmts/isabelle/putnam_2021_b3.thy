theory putnam_2021_b3 imports
Complex_Main
"HOL-Analysis.Derivative"
"HOL-Analysis.Finite_Cartesian_Product"
"HOL-Analysis.Set_Integral"
"HOL-Analysis.Lebesgue_Measure"
begin

definition putnam_2021_b3_solution :: bool where
  "putnam_2021_b3_solution \<equiv> True"
(* True *)
theorem putnam_2021_b3:
  fixes C2diff :: "(real \<times> real \<Rightarrow> real) \<Rightarrow> bool"
  and hx hy hxx hxy hyx hyy ::
    "(real \<times> real \<Rightarrow> real) \<Rightarrow> real \<times> real \<Rightarrow> real"
  and rho :: "(real \<times> real \<Rightarrow> real) \<Rightarrow> real \<times> real \<Rightarrow> real"
  and circint :: "real \<times> real \<Rightarrow> real \<Rightarrow> (real \<times> real) set"
  defines "hx \<equiv> \<lambda>h (x, y). deriv (\<lambda>u. h (u, y)) x"
  and "hy \<equiv> \<lambda>h (x, y). deriv (\<lambda>v. h (x, v)) y"
  and "hxx \<equiv> \<lambda>h (x, y). deriv (\<lambda>u. hx h (u, y)) x"
  and "hxy \<equiv> \<lambda>h (x, y). deriv (\<lambda>v. hx h (x, v)) y"
  and "hyx \<equiv> \<lambda>h (x, y). deriv (\<lambda>u. hy h (u, y)) x"
  and "hyy \<equiv> \<lambda>h (x, y). deriv (\<lambda>v. hy h (x, v)) y"
  and "C2diff \<equiv> \<lambda>h.
    (\<forall>y.
      (\<lambda>x. h (x, y)) differentiable_on UNIV \<and>
      (\<lambda>x. hx h (x, y)) differentiable_on UNIV \<and>
      (\<lambda>x. hy h (x, y)) differentiable_on UNIV) \<and>
    (\<forall>x.
      (\<lambda>y. h (x, y)) differentiable_on UNIV \<and>
      (\<lambda>y. hx h (x, y)) differentiable_on UNIV \<and>
      (\<lambda>y. hy h (x, y)) differentiable_on UNIV) \<and>
    continuous_on UNIV h \<and>
    continuous_on UNIV (hx h) \<and>
    continuous_on UNIV (hy h) \<and>
    continuous_on UNIV (hxx h) \<and>
    continuous_on UNIV (hxy h) \<and>
    continuous_on UNIV (hyx h) \<and>
    continuous_on UNIV (hyy h)"
  and "rho \<equiv> \<lambda>h (x, y). y * hx h (x, y) - x * hy h (x, y)"
  and "circint \<equiv> \<lambda> c r. {p :: real \<times> real. dist p c < r}"
  shows "(\<forall>h :: real \<times> real \<Rightarrow> real.
    C2diff h \<longrightarrow>
    (\<forall>d>0. \<forall>r>0. d > r \<longrightarrow>
      (\<exists>c :: real \<times> real.
        dist c 0 = d \<and>
        set_lebesgue_integral lebesgue (circint c r) (rho h) = 0)))
      \<longleftrightarrow> putnam_2021_b3_solution"
  sorry

end
