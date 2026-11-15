theory circle_average
  imports Main
begin

locale circle_average_setup =
  fixes zero     :: "'r"
    and add      :: "'r \<Rightarrow> 'r \<Rightarrow> 'r"     (infixl "+C" 65)
    and integral :: "('r \<Rightarrow> 'r) \<Rightarrow> 'r"
  assumes add_zero      : "\<And>x. x +C zero = x"
    and   add_comm      : "\<And>x y. x +C y = y +C x"
    and   add_assoc     : "\<And>x y z. (x +C y) +C z = x +C (y +C z)"
    and   integral_ext  : "\<And>g h. (\<forall>\<theta>. g \<theta> = h \<theta>) \<Longrightarrow> integral g = integral h"
    and   integral_const: "\<And>c. integral (\<lambda>_. c) = c"
    and   integral_add  : "\<And>f g. integral (\<lambda>\<theta>. f \<theta> +C g \<theta>) = integral f +C integral g"
    and   integral_shift: "\<And>f c. integral (\<lambda>\<theta>. f (\<theta> +C c)) = integral f"
begin





definition circleMap :: "'r \<Rightarrow> 'r \<Rightarrow> 'r"
  where "circleMap c \<theta> \<equiv> \<theta> +C c"

definition circleAverage :: "('r \<Rightarrow> 'r) \<Rightarrow> 'r \<Rightarrow> 'r"
  where "circleAverage f c \<equiv> integral (\<lambda>\<theta>. f (circleMap c \<theta>))"





lemma circleMap_zero: "circleMap zero \<theta> = \<theta>"
  sorry
lemma circleAverage_zero: "circleAverage f zero = integral f"
  sorry
lemma circleAverage_add:
  "circleAverage (\<lambda>z. f z +C g z) c =
   circleAverage f c +C circleAverage g c"
  sorry
lemma circleAverage_fun_add:
  "circleAverage (\<lambda>z. f (z +C c)) zero = circleAverage f c"
  sorry
lemma circleMap_add:
  "circleMap (c +C d) \<theta> = circleMap c (circleMap d \<theta>)"
  sorry
lemma circleAverage_shift:
  "circleAverage f (c +C d) = circleAverage (\<lambda>z. f (z +C d)) c"
  sorry
lemma circleAverage_const:
  "circleAverage (\<lambda>_. k) c = k"
  sorry
lemma circleAverage_add_const:
  "circleAverage (\<lambda>z. f z +C k) c = circleAverage f c +C k"
  sorry
lemma circleAverage_comm_add:
  "circleAverage (\<lambda>z. f z +C g z) c =
   circleAverage (\<lambda>z. g z +C f z) c"
  sorry
lemma circleAverage_add_assoc:
  "circleAverage (\<lambda>z. (f z +C g z) +C h z) c =
   circleAverage f c +C (circleAverage g c +C circleAverage h c)"
  sorry
lemma circleAverage_center_comm:
  "circleAverage f (c +C d) = circleAverage f (d +C c)"
  sorry
lemma circleAverage_center_independent:
  "circleAverage f c = integral f"
  sorry
lemma circleAverage_center_eq:
  "circleAverage f c = circleAverage f d"
  sorry
lemma circleAverage_idempotent:
  "circleAverage (\<lambda>z. circleAverage f z) c = circleAverage f c"
  sorry
lemma circleAverage_of_zero_integral:
  "integral f = zero \<Longrightarrow> circleAverage f c = zero"
  sorry
lemma circleAverage_linear:
  "circleAverage (\<lambda>z. f z +C g z) c =
   circleAverage f c +C circleAverage g c"
  sorry
lemma circleAverage_shift_commute:
  "circleAverage (\<lambda>z. f (circleMap d z)) c =
   circleAverage f (c +C d)"
  sorry
end

end
