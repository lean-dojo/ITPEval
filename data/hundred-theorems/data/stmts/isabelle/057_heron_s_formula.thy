(*
  Statement-only formalization of Heron's formula from Hundred Theorems
  item 057. The triangle area is expressed by the Gram determinant of two
  side vectors, which is valid in every real inner-product space. This file
  contains no proof.
*)

theory Herons_Formula
  imports "HOL-Analysis.Inner_Product"
begin

definition triangle_area ::
    "'a::real_inner \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> real"
  where
    "triangle_area A B C =
      (1 / 2) * sqrt
        (norm (A - B) ^ 2 * norm (C - B) ^ 2
          - inner (A - B) (C - B) ^ 2)"

theorem herons_formula:
  fixes A B C :: "'a::real_inner"
  shows
    "let a = dist A B;
         b = dist C B;
         c = dist A C;
         s = (a + b + c) / 2
     in triangle_area A B C = sqrt (s * (s - a) * (s - b) * (s - c))"
  sorry

end
