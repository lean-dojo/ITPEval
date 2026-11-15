(*
  Statement-only formalization of Logipedia corpus artifact
  nat.monotonic_lt_times_l, catalog title "nat.monotonic_lt_times_l": for
  every positive natural number c, multiplication by c on the right strictly
  preserves the natural-number order. This file contains no proof.
*)

theory monotonic_lt_times_l
  imports Main
begin

theorem monotonic_lt_times_l:
  "\<forall>c :: nat. 0 < c \<longrightarrow>
    (\<forall>x y :: nat. x < y \<longrightarrow> x * c < y * c)"
  sorry

end
