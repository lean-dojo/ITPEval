(*
  Statement-only formalization of the thousand-theorems corpus artifact Q193286,
  "Rolle's theorem": a continuous real-valued function with equal values at
  the endpoints of a nondegenerate closed interval has an interior point where
  its derivative, defined as zero when it does not exist, is zero. This file
  contains no proof.
*)

theory Q193286_rolle_s_theorem
  imports Complex_Main
begin

definition q193286_lean_deriv :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real" where
  "q193286_lean_deriv f x =
    (if \<exists>d. DERIV f x :> d then (SOME d. DERIV f x :> d) else 0)"

theorem q193286_exists_deriv_eq_zero:
  fixes f :: "real \<Rightarrow> real"
    and a b :: real
  assumes "a < b"
    and "continuous_on {a..b} f"
    and "f a = f b"
  shows "\<exists>c \<in> {a<..<b}. q193286_lean_deriv f c = 0"
  sorry

end
