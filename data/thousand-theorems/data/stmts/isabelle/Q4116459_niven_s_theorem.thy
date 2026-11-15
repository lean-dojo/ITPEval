(*
  Statement-only formalization of the thousand-theorems corpus artifact
  Q4116459 (thousand-theorems__isabelle__Q4116459), "Niven's theorem": if a
  real angle is a rational multiple of pi and has rational cosine, then its
  cosine is one of -1, -1/2, 0, 1/2, or 1. This file contains no proof.
*)

theory Q4116459_niven_s_theorem
  imports Complex_Main
begin

theorem niven:
  fixes theta :: real
  assumes rational_angle:
    "\<exists>r :: rat. theta = of_rat r * pi"
    and rational_cosine:
    "\<exists>q :: rat. cos theta = of_rat q"
  shows "cos theta \<in> {(-1 :: real), -1 / 2, 0, 1 / 2, 1}"
  sorry

end
