theory putnam_1988_a3 imports
Complex_Main
begin

definition putnam_1988_a3_solution :: "real set" where
"putnam_1988_a3_solution \<equiv> {x :: real. x > 1 / 2}"
theorem putnam_1988_a3:
  shows "{x :: real. convergent (\<lambda> t :: nat.
    \<Sum> n = 1..t. ((1 / real n) / sin (1 / real n) - 1) powr x)}
    = putnam_1988_a3_solution"
  sorry

end
