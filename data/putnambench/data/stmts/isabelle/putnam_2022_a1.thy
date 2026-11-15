theory putnam_2022_a1 imports Complex_Main
begin

definition putnam_2022_a1_solution :: "(real \<times> real) set" where
  "putnam_2022_a1_solution \<equiv> {(a, b).
    (a = 0 \<and> b = 0) \<or>
    1 \<le> abs a \<or>
    (0 < abs a \<and> abs a < 1 \<and>
      (let rm = (1 - sqrt (1 - a^2)) / a;
           rp = (1 + sqrt (1 - a^2)) / a
       in b < ln (1 + rm^2) - a * rm \<or>
          b > ln (1 + rp^2) - a * rp))}"
(* The two bounds are the tangent-line intercepts at the critical points rm and rp. *)
theorem putnam_2022_a1:
  shows "{(a, b). \<exists>! x :: real. a * x + b = ln (1 + x^2)} = putnam_2022_a1_solution"
  sorry

end
