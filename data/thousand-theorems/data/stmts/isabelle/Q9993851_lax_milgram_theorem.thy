(*
  Statement-only formalization of the thousand-theorems corpus artifact
  Q9993851 (thousand-theorems__isabelle__Q9993851), "Lax–Milgram theorem":
  every coercive bounded bilinear form on a real Hilbert space induces a
  continuous linear equivalence of that space with itself. This file contains
  no proof.
*)

theory Q9993851_lax_milgram_theorem
  imports "HOL-Analysis.Inner_Product"
begin

theorem q9993851_lax_milgram:
  fixes B :: "'a::{real_inner,complete_space} \<Rightarrow> 'a \<Rightarrow> real"
  assumes bounded: "bounded_bilinear B"
    and coercive:
      "\<exists>C::real. 0 < C \<and> (\<forall>u. C * norm u * norm u \<le> B u u)"
  shows
    "\<exists>T S :: 'a \<Rightarrow> 'a.
      bounded_linear T \<and>
      bounded_linear S \<and>
      (\<forall>x. S (T x) = x) \<and>
      (\<forall>x. T (S x) = x) \<and>
      (\<forall>v w. inner (T v) w = B v w)"
  sorry

end
