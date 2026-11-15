section \<open>Ferrari's formula for solving quartic equations\<close>

theory Ferraris_Formula
  imports 
    Polynomial_Factorization.Explicit_Roots
    Polynomial_Interpolation.Ring_Hom_Poly
    Complex_Geometry.More_Complex
begin

subsection \<open>Translation to depressed case\<close>

text \<open>Solving an arbitrary quartic equation can easily be turned into the depressed case, i.e., where
  there is no cubic part.\<close>

lemma to_depressed_quartic: fixes a4 :: "'a :: field_char_0"
  assumes a4: "a4 \<noteq> 0" 
  and b: "b = a3 / a4" 
  and c: "c = a2 / a4" 
  and d: "d = a1 / a4" 
  and e: "e = a0 / a4" 
  and p: "p = c - (3/8) * b^2" 
  and q: "q = (b^3 - 4*b*c + 8 * d) / 8" 
  and r: "r = ( -3 * b^4 + 256 * e - 64 * b * d + 16 * b^2 * c) / 256" 
  and x: "x = y - b/4" 
shows "a4 * x^4 + a3 * x^3 + a2 * x^2 + a1 * x + a0 = 0 
  \<longleftrightarrow> y^4 + p * y^2 + q * y + r = 0" 
  by sorry

lemma biquadratic_solution: fixes p q :: "'a :: field_char_0"
  shows "y^4 + p * y^2 + q = 0 \<longleftrightarrow> (\<exists> z. z^2 + p * z + q = 0 \<and> z = y^2)" 
  by sorry

subsection \<open>Solving the depressed case via Ferrari's formula\<close>

lemma depressed_quartic_Ferrari: fixes p q r :: "'a :: field_char_0" 
  assumes cubic_root: "8*m^3 + (8 * p) * m^2 + (2 * p^2 - 8 * r) * m - q^2 = 0" 
  and q0: "q \<noteq> 0"  \<comment> \<open>otherwise m might be zero, so a is zero and then there is a division by zero in b1 and b2\<close>
  and sqrt: "a * a = 2 * m"  (* a = sqrt(2m), where the square-root might not be defined *)
  and b1: "b1 = p / 2 + m - q / (2 * a)" 
  and b2: "b2 = p / 2 + m + q / (2 * a)" 
  shows "y^4 + p * y^2 + q * y + r = 0 \<longleftrightarrow> poly [:b1,a,1:] y = 0 \<or> poly [:b2,-a,1:] y = 0" 
  by sorry


end