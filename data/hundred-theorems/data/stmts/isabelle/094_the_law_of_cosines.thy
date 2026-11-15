(*
  File:    Triangle.thy
  Author:  Manuel Eberl <manuel@pruvisto.org>

  Sine and cosine laws, angle sum in a triangle, congruence theorems,
  Isosceles Triangle Theorem
*)

section \<open>Basic Properties of Triangles\<close>
theory Triangle
imports
  Angles
begin

text \<open>
  We prove a number of basic geometric properties of triangles. All theorems hold
  in any real inner product space.
\<close>
subsection \<open>Thales' theorem\<close>

theorem thales:
  fixes A B C :: "'a :: real_inner"
  assumes "dist B (midpoint A C) = dist A C / 2"
  shows   "orthogonal (A - B) (C - B)"
  by sorry

subsection \<open>Sine and cosine laws\<close>

text \<open>
  The proof of the Law of Cosines follows trivially from the definition of the angle,
  the definition of the norm in vector spaces with an inner product and the bilinearity
  of the inner product.
\<close>

lemma cosine_law_vector:
  "norm (u - v) ^ 2 = norm u ^ 2 + norm v ^ 2 - 2 * norm u * norm v * cos (vangle u v)"
  by sorry

lemma cosine_law_triangle:
  "dist b c ^ 2 = dist a b ^ 2 + dist a c ^ 2 - 2 * dist a b * dist a c * cos (angle b a c)"
  by sorry


text \<open>
  According to our definition, angles are always between $0$ and $\pi$ and therefore,
  the sign of an angle is always non-negative. We can therefore look at
  $\sin(\alpha)^2$, which we can express in terms of $\cos(\alpha)$ using the
  identity $\sin(\alpha)^2 + \cos(\alpha)^2 = 1$. The remaining proof is then a
  trivial consequence of the definitions.
\<close>
lemma sine_law_triangle:
  "sin (angle a b c) * dist b c = sin (angle b a c) * dist a c" (is "?A = ?B")
  by sorry


text \<open>
  The following forms of the Law of Sines/Cosines are more convenient for eliminating
  sines/cosines from a goal completely.
\<close>

lemma cosine_law_triangle':
  "2 * dist a b * dist a c * cos (angle b a c) = (dist a b ^ 2 + dist a c ^ 2 - dist b c ^ 2)"
  by sorry

lemma cosine_law_triangle'':
  "cos (angle b a c) = (dist a b ^ 2 + dist a c ^ 2 - dist b c ^ 2) / (2 * dist a b * dist a c)"
  by sorry

lemma sine_law_triangle':
  "b \<noteq> c \<Longrightarrow> sin (angle a b c) = sin (angle b a c) * dist a c / dist b c"
  by sorry

lemma sine_law_triangle'':
  "b \<noteq> c \<Longrightarrow> sin (angle c b a) = sin (angle b a c) * dist a c / dist b c"
  by sorry


subsection \<open>Sum of angles\<close>

context
begin

private lemma gather_squares: "a * (a * b) = a^2 * (b :: real)"
  by (simp_all add: power2_eq_square)

private lemma eval_power: "x ^ numeral n = x * x ^ pred_numeral n"
  by (subst numeral_eq_Suc, subst power_Suc) simp

text \<open>
  The proof that the sum of the angles in a triangle is $\pi$ is somewhat more
  involved. Following the HOL Light proof by John Harrison, we first prove
  that $\cos(\alpha + \beta + \gamma) = -1$ and $\alpha + \beta + \gamma \in [0;3\pi)$,
  which then implies the theorem.

  The main work is proving $\cos(\alpha + \beta + \gamma)$. This is done using the
  addition theorems for the sine and cosine, then using the Laws of Sines to eliminate
  all $\sin$ terms save $\sin(\gamma)^2$, which only appears squared in the remaining goal.
  We then use $\sin(\gamma)^2 = 1 - \cos(\gamma)^2$ to eliminate this term and apply
  the law of cosines to eliminate this term as well.

  The remaining goal is a non-linear equation containing only the length of the sides
  of the triangle. It can be shown by simple algebraic rewriting.
\<close>
lemma angle_sum_triangle:
  assumes "a \<noteq> b \<or> b \<noteq> c \<or> a \<noteq> c"
  shows   "angle c a b + angle a b c + angle b c a = pi"
  by sorry

end


subsection \<open>Congruence Theorems\<close>

text \<open>
  If two triangles agree on two angles at a non-degenerate side, the third angle
  must also be equal.
\<close>
lemma similar_triangle_aa:
  assumes "b1 \<noteq> c1" "b2 \<noteq> c2"
  assumes "angle a1 b1 c1 = angle a2 b2 c2"
  assumes "angle b1 c1 a1 = angle b2 c2 a2"
  shows   "angle b1 a1 c1 = angle b2 a2 c2"
  by sorry

text \<open>
  A triangle is defined by its three angles and the lengths of three sides up to congruence.
  Two triangles are congruent if they have their angles are the same and their sides have
  the same length.
\<close>

locale congruent_triangle =
  fixes a1 b1 c1 :: "'a :: real_inner" and a2 b2 c2 :: "'b :: real_inner"
  assumes sides':  "dist a1 b1 = dist a2 b2" "dist a1 c1 = dist a2 c2" "dist b1 c1 = dist b2 c2"
      and angles': "angle b1 a1 c1 = angle b2 a2 c2" "angle a1 b1 c1 = angle a2 b2 c2"
                   "angle a1 c1 b1 = angle a2 c2 b2"
begin

lemma sides:
  "dist a1 b1 = dist a2 b2" "dist a1 c1 = dist a2 c2" "dist b1 c1 = dist b2 c2"
  "dist b1 a1 = dist a2 b2" "dist c1 a1 = dist a2 c2" "dist c1 b1 = dist b2 c2"
  "dist a1 b1 = dist b2 a2" "dist a1 c1 = dist c2 a2" "dist b1 c1 = dist c2 b2"
  "dist b1 a1 = dist b2 a2" "dist c1 a1 = dist c2 a2" "dist c1 b1 = dist c2 b2"
  by sorry

lemma angles:
  "angle b1 a1 c1 = angle b2 a2 c2" "angle a1 b1 c1 = angle a2 b2 c2" "angle a1 c1 b1 = angle a2 c2 b2"
  "angle c1 a1 b1 = angle b2 a2 c2" "angle c1 b1 a1 = angle a2 b2 c2" "angle b1 c1 a1 = angle a2 c2 b2"
  "angle b1 a1 c1 = angle c2 a2 b2" "angle a1 b1 c1 = angle c2 b2 a2" "angle a1 c1 b1 = angle b2 c2 a2"
  "angle c1 a1 b1 = angle c2 a2 b2" "angle c1 b1 a1 = angle c2 b2 a2" "angle b1 c1 a1 = angle b2 c2 a2"
  by sorry

end

lemmas congruent_triangleD = congruent_triangle.sides congruent_triangle.angles



text \<open>
  Given two triangles that agree on a subset of its side lengths and angles that are
  sufficient to define a triangle uniquely up to congruence, one can conclude that they
  must also agree on all remaining quantities, i.e. that they are congruent.

  The following four congruence theorems state what constitutes such a uniquely-defining
  subset of quantities. Each theorem states in its name which quantities are required and
  in which order (clockwise or counter-clockwise): an ``s'' stands for a side,
  an ``a'' stands for an angle.

  The lemma ``congruent-triangleI-sas, for example, requires that two adjacent sides and the
  angle inbetween are the same in both triangles.
\<close>

lemma congruent_triangleI_sss:
  fixes a1 b1 c1 :: "'a :: real_inner" and a2 b2 c2 :: "'b :: real_inner"
  assumes "dist a1 b1 = dist a2 b2"
  assumes "dist b1 c1 = dist b2 c2"
  assumes "dist a1 c1 = dist a2 c2"
  shows   "congruent_triangle a1 b1 c1 a2 b2 c2"
  by sorry

lemmas congruent_triangle_sss = congruent_triangleD[OF congruent_triangleI_sss]

lemma congruent_triangleI_sas:
  assumes "dist a1 b1 = dist a2 b2"
  assumes "dist b1 c1 = dist b2 c2"
  assumes "angle a1 b1 c1 = angle a2 b2 c2"
  shows   "congruent_triangle a1 b1 c1 a2 b2 c2"
  by sorry

lemmas congruent_triangle_sas = congruent_triangleD[OF congruent_triangleI_sas]

lemma congruent_triangleI_aas:
  assumes "angle a1 b1 c1 = angle a2 b2 c2"
  assumes "angle b1 c1 a1 = angle b2 c2 a2"
  assumes "dist a1 b1 = dist a2 b2"
  assumes "\<not>collinear {a1,b1,c1}"
  shows   "congruent_triangle a1 b1 c1 a2 b2 c2"
  by sorry

lemmas congruent_triangle_aas = congruent_triangleD[OF congruent_triangleI_aas]

lemma congruent_triangleI_asa:
  assumes "angle a1 b1 c1 = angle a2 b2 c2"
  assumes "dist a1 b1 = dist a2 b2"
  assumes "angle b1 a1 c1 = angle b2 a2 c2"
  assumes "\<not>collinear {a1, b1, c1}"
  shows   "congruent_triangle a1 b1 c1 a2 b2 c2"
  by sorry

lemmas congruent_triangle_asa = congruent_triangleD[OF congruent_triangleI_asa]


subsection \<open>Isosceles Triangle Theorem\<close>

text \<open>
  We now prove the Isosceles Triangle Theorem: in a triangle where two sides have
  the same length, the two angles that are adjacent to only one of the two sides
  must be equal.
\<close>
lemma isosceles_triangle:
  assumes "dist a c = dist b c"
  shows   "angle b a c = angle a b c"
  by sorry


text \<open>
  For the non-degenerate case (i.e. the three points are not collinear), We also
  prove the converse.
\<close>
lemma isosceles_triangle_converse:
  assumes "angle a b c = angle b a c" "\<not>collinear {a,b,c}"
  shows   "dist a c = dist b c"
  by sorry


subsection\<open>Contributions by Lukas Bulwahn\<close>
  
lemma Pythagoras:
  fixes A B C :: "'a :: real_inner"
  assumes "orthogonal (A - C) (B - C)"
  shows "(dist B C) ^ 2 + (dist C A) ^ 2 = (dist A B) ^ 2"
  by sorry

lemma isosceles_triangle_orthogonal_on_midpoint:
  fixes A B C :: "'a :: euclidean_space"
  assumes "dist C A = dist C B"
  shows "orthogonal (C - midpoint A B) (A - midpoint A B)"
  by sorry

end
