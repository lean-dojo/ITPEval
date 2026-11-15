(*
  Statement-only formalization of the thousand-theorems corpus artifact
  Q203565 (thousand-theorems__isabelle__Q203565), "Solutions of a general
  cubic equation": Cardano data characterize the three roots of a cubic over
  a field in which 2 and 3 are invertible. This file contains no proof.
*)

theory Q203565_solutions_of_a_general_cubic_equation
  imports Main
begin

definition q203565_is_primitive_cube_root :: "'a::field \<Rightarrow> bool" where
  "q203565_is_primitive_cube_root w \<longleftrightarrow>
    w ^ 3 = 1 \<and> (\<forall>n::nat. w ^ n = 1 \<longrightarrow> 3 dvd n)"

theorem q203565_cubic_eq_zero_iff:
  fixes a b c d omega p q r s t x :: "'a::field"
  assumes two_nonzero: "(2::'a) \<noteq> 0"
    and three_nonzero: "(3::'a) \<noteq> 0"
    and a_nonzero: "a \<noteq> 0"
    and omega_primitive: "q203565_is_primitive_cube_root omega"
    and p_def: "p = (3 * a * c - b ^ 2) / (9 * a ^ 2)"
    and p_nonzero: "p \<noteq> 0"
    and q_def:
      "q = (9 * a * b * c - 2 * b ^ 3 - 27 * a ^ 2 * d) / (54 * a ^ 3)"
    and r_square: "r ^ 2 = q ^ 2 + p ^ 3"
    and s_cube: "s ^ 3 = q + r"
    and ts_product: "t * s = p"
  shows "a * x ^ 3 + b * x ^ 2 + c * x + d = 0 \<longleftrightarrow>
    x = s - t - b / (3 * a) \<or>
    x = s * omega - t * omega ^ 2 - b / (3 * a) \<or>
    x = s * omega ^ 2 - t * omega - b / (3 * a)"
  sorry

end
