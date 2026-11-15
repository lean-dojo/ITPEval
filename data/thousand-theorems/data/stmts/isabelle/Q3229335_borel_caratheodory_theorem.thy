(*
  Statement-only formalization of the thousand-theorems corpus artifact
  Q3229335 (thousand-theorems__isabelle__Q3229335),
  "Borel–Carathéodory theorem": for positive real M and positive radius R, a
  complex-differentiable function on the open disc of radius R whose real part
  is bounded above by M satisfies the Borel–Carathéodory norm estimate at every
  point of the disc. This file contains no proof.
*)

theory Q3229335_borel_caratheodory_theorem
  imports "HOL-Analysis.Complex_Analysis_Basics"
begin

theorem q3229335_borel_caratheodory:
  fixes f :: "complex \<Rightarrow> complex"
    and M R :: real
    and z :: complex
  assumes positive_bound: "0 < M"
    and differentiable: "f holomorphic_on ball 0 R"
    and real_part_bound: "\<forall>w \<in> ball 0 R. Re (f w) \<le> M"
    and positive_radius: "0 < R"
    and point_in_disc: "z \<in> ball 0 R"
  shows
    "norm (f z) \<le>
      2 * M * norm z / (R - norm z) +
      norm (f 0) * (R + norm z) / (R - norm z)"
  sorry

end
