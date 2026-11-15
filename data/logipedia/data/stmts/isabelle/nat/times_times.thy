(*
  Statement-only formalization of Logipedia corpus artifact nat.times_times,
  catalog title nat.times_times: multiplication on natural numbers commutes
  in the first two factors of a three-factor product. This file contains no proof.
*)

theory times_times
  imports Main
begin

theorem times_times:
  "\<forall>x y z :: nat. x * (y * z) = y * (x * z)"
  sorry

end
