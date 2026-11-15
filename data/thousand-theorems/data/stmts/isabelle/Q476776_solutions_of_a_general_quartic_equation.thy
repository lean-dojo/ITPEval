(*
  Statement-only formalization of the thousand-theorems corpus artifact
  Q476776 (thousand-theorems__isabelle__Q476776), "Solutions of a general
  quartic equation": Ferrari resolvent data characterize the four roots of a
  general quartic over a field in which 2 is invertible. This file contains no
  proof.
*)

theory Q476776_solutions_of_a_general_quartic_equation
  imports Main
begin

theorem q476776_quartic_eq_zero_iff:
  fixes a b c d e p q r u s v w x :: "'a::field"
  assumes two_nonzero: "(2::'a) \<noteq> 0"
    and a_nonzero: "a \<noteq> 0"
    and p_def: "p = (8 * a * c - 3 * b ^ 2) / (8 * a ^ 2)"
    and q_def: "q = (b ^ 3 - 4 * a * b * c + 8 * a ^ 2 * d) / (8 * a ^ 3)"
    and q_nonzero: "q \<noteq> 0"
    and r_def:
      "r = (16 * a * b ^ 2 * c + 256 * a ^ 3 * e - 3 * b ^ 4 -
        64 * a ^ 2 * b * d) / (256 * a ^ 4)"
    and u_resolvent: "u ^ 3 - p * u ^ 2 - 4 * r * u + 4 * p * r - q ^ 2 = 0"
    and s_square: "s ^ 2 = u - p"
    and v_square: "v ^ 2 = 4 * s ^ 2 - 8 * (u - q / s)"
    and w_square: "w ^ 2 = 4 * s ^ 2 - 8 * (u + q / s)"
  shows "a * x ^ 4 + b * x ^ 3 + c * x ^ 2 + d * x + e = 0 \<longleftrightarrow>
    x = (-2 * s - v) / 4 - b / (4 * a) \<or>
    x = (-2 * s + v) / 4 - b / (4 * a) \<or>
    x = (2 * s - w) / 4 - b / (4 * a) \<or>
    x = (2 * s + w) / 4 - b / (4 * a)"
  sorry

end
