(*
  Statement-only formalization of "The Isoperimetric Theorem" from Hundred Theorems item 043.
  The statement uses Isabelle/HOL's native path, planar-inside, sphere, path-length, and
  Lebesgue-measure notions, with complex numbers representing the Euclidean plane.
  This file contains no proof.
*)

theory Isoperimetric_Theorem
  imports
    "HOL-Analysis.Analysis"
begin

theorem isoperimetric_theorem:
  fixes L :: real
    and g :: "real \<Rightarrow> complex"
  assumes "rectifiable_path g"
    and "simple_path g"
    and "pathfinish g = pathstart g"
    and "path_length g = L"
  shows "measure lebesgue (inside (path_image g)) \<le> L ^ 2 / (4 * pi) \<and>
    (measure lebesgue (inside (path_image g)) = L ^ 2 / (4 * pi)
      \<longrightarrow> (\<exists>a r. path_image g = sphere a r))"
  sorry

end
