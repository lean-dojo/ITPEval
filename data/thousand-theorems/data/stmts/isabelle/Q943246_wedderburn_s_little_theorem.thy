(*
  Statement-only formalization of thousand-theorems corpus artifact Q943246
  (thousand-theorems__isabelle__Q943246), "Wedderburn's little theorem":
  all elements of every finite division ring commute under multiplication,
  equivalently every finite division ring is a field. This file contains no
  proof.
*)

theory Q943246_wedderburn_s_little_theorem
  imports Main
begin

theorem littleWedderburn:
  fixes x y :: "'a::division_ring"
  assumes "finite (UNIV :: 'a set)"
  shows "x * y = y * x"
  sorry

end
