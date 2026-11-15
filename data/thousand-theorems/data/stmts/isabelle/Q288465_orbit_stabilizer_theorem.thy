(*
  Statement-only formalization of thousand-theorems corpus artifact Q288465
  (thousand-theorems__isabelle__Q288465), "Orbit-stabilizer theorem": for a
  group acting on a type, the orbit of a point is canonically equivalent to
  the quotient of the group by that point's stabilizer. This file contains no
  proof.
*)

theory Q288465_orbit_stabilizer_theorem
  imports Main
begin

definition q288465_orbit ::
    "('g::group_add \<Rightarrow> 'x \<Rightarrow> 'x) \<Rightarrow> 'x \<Rightarrow> 'x set"
  where
    "q288465_orbit act b = {x. \<exists>g. act g b = x}"

definition q288465_stabilizer ::
    "('g::group_add \<Rightarrow> 'x \<Rightarrow> 'x) \<Rightarrow> 'x \<Rightarrow> 'g set"
  where
    "q288465_stabilizer act b = {g. act g b = b}"

definition q288465_left_coset ::
    "'g::group_add set \<Rightarrow> 'g \<Rightarrow> 'g set"
  where
    "q288465_left_coset H g = (\<lambda>h. g + h) ` H"

definition q288465_quotient_stabilizer ::
    "('g::group_add \<Rightarrow> 'x \<Rightarrow> 'x) \<Rightarrow> 'x \<Rightarrow> 'g set set"
  where
    "q288465_quotient_stabilizer act b =
      q288465_left_coset (q288465_stabilizer act b) ` UNIV"

theorem orbit_stabilizer_equivalence:
  fixes act :: "'g::group_add \<Rightarrow> 'x \<Rightarrow> 'x"
    and b :: "'x"
  assumes action_zero: "\<And>x. act 0 x = x"
    and action_add: "\<And>g h x. act (g + h) x = act g (act h x)"
  shows "\<exists>to_orbit :: 'g set \<Rightarrow> 'x.
    bij_betw to_orbit
      (q288465_quotient_stabilizer act b)
      (q288465_orbit act b) \<and>
    (\<forall>g. to_orbit
      (q288465_left_coset (q288465_stabilizer act b) g) = act g b)"
  sorry

end
