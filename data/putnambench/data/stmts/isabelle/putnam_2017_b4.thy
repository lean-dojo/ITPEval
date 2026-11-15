theory putnam_2017_b4 imports
Complex_Main
begin

definition putnam_2017_b4_solution :: real where
  "putnam_2017_b4_solution \<equiv> (ln 2)^2"
(* (ln 2) ^ 2 *)
theorem putnam_2017_b4:
  shows "(\<lambda>k :: nat.
    3 * ln (real (4 * k + 2)) / real (4 * k + 2) -
    ln (real (4 * k + 3)) / real (4 * k + 3) -
    ln (real (4 * k + 4)) / real (4 * k + 4) -
    ln (real (4 * k + 5)) / real (4 * k + 5))
      sums putnam_2017_b4_solution"
  sorry

end
