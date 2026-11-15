(*
  Statement-only formalization of Logipedia corpus artifact
  nat.monotonic_lt_times_r, catalog title "nat.monotonic_lt_times_r": for
  every positive natural number c, multiplication by c on the left strictly
  preserves the natural-number order. This file contains no proof.
*)

theory monotonic_lt_times_r
  imports Main
begin

theorem monotonic_lt_times_r:
  "\<forall>c :: nat. 0 < c \<longrightarrow>
    (\<forall>x y :: nat. x < y \<longrightarrow> c * x < c * y)"
  sorry

end
