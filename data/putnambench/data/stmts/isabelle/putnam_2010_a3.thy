(*
  Statement-only formalization of PutnamBench artifact putnam_2010_a3,
  concerning a bounded continuously differentiable solution of a
  constant-coefficient first-order partial differential equation.
  This file contains no proof.
*)

theory putnam_2010_a3
  imports Complex_Main
begin

theorem putnam_2010_a3:
  fixes h :: "real \<times> real \<Rightarrow> real"
    and a b M :: real
  assumes hC1_pde:
    "\<exists>hx hy :: real \<times> real \<Rightarrow> real.
      continuous_on UNIV hx \<and> continuous_on UNIV hy \<and>
      (\<forall>x y.
        ((\<lambda>u. h (u, y)) has_real_derivative hx (x, y)) (at x) \<and>
        ((\<lambda>v. h (x, v)) has_real_derivative hy (x, y)) (at y) \<and>
        h (x, y) = a * hx (x, y) + b * hy (x, y))"
    and hbounded: "\<forall>x y. \<bar>h (x, y)\<bar> \<le> M"
  shows "h = (\<lambda>_. 0)"
  sorry

end
