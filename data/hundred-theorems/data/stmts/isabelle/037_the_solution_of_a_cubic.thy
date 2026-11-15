section \<open>Algorithms to compute all complex and real roots of a cubic polynomial\<close>

theory Cubic_Polynomials
  imports 
    Cardanos_Formula
    Complex_Roots
begin

text \<open>The real case where a result is only delivered if the discriminant is negative\<close>

definition solve_depressed_cubic_Cardano_real :: "real \<Rightarrow> real \<Rightarrow> real option" where
  "solve_depressed_cubic_Cardano_real e f = (
    if e = 0 then Some (root 3 (-f)) else
     let v = - (e ^ 3 / 27) in
     case rroots2 [:v,f,1:] of 
       [u,_] \<Rightarrow> let rt = root 3 u in Some (rt - e / (3 * rt))
     | _ \<Rightarrow> None)" 

lemma solve_depressed_cubic_Cardano_real: 
  assumes "solve_depressed_cubic_Cardano_real e f = Some y" 
  shows "{y. y^3 + e * y + f = 0} = {y}"
  by sorry

text \<open>The complex case\<close>

definition solve_depressed_cubic_complex :: "complex \<Rightarrow> complex \<Rightarrow> complex list" where
  "solve_depressed_cubic_complex e f = (let
          ys = (if e = 0 then all_croots 3 (- f) else (let
       u = hd (croots2 [: - (e ^ 3 / 27) ,f,1:]); 
       zs = all_croots 3 u 
       in map (\<lambda> z. z - e / (3 * z)) zs))
      in remdups ys)" 

lemma solve_depressed_cubic_complex_code[code]: 
  "solve_depressed_cubic_complex e f = (let
          ys = (if e = 0 then all_croots 3 (- f) else (let
            f2 = f / 2;
            u = - f2 + csqrt (f2^2 + e ^ 3 / 27);
            zs = all_croots 3 u 
            in map (\<lambda> z. z - e / (3 * z)) zs))
      in remdups ys)" 
  by sorry


lemma solve_depressed_cubic_complex: "y \<in> set (solve_depressed_cubic_complex e f) 
  \<longleftrightarrow> (y^3 + e * y + f = 0)"
  by sorry

text \<open>For the general real case, we first try Cardano with negative discrimiant and only if it is not applicable,
   then we go for the calculation using complex numbers. Note that for for non-negative delta 
   no filter is required to identify the real roots from the list of complex roots, since in that case we 
   already know that all roots are real.\<close>
definition solve_depressed_cubic_real :: "real \<Rightarrow> real \<Rightarrow> real list" where
  "solve_depressed_cubic_real e f = (case solve_depressed_cubic_Cardano_real e f 
      of Some y \<Rightarrow> [y] 
       | None \<Rightarrow> map Re (solve_depressed_cubic_complex (of_real e) (of_real f)))"

lemma solve_depressed_cubic_real_code[code]: "solve_depressed_cubic_real e f =
  (if e = 0 then [root 3 (-f)] else 
   let v = e ^ 3 / 27; 
       f2 = f / 2;
       f2v = f2^2 + v in
   if f2v > 0 then 
     let u = -f2 + sqrt f2v;
         rt = root 3 u
      in [rt - e / (3 * rt)]
  else 
  let ce3 = of_real e / 3; 
      u = - of_real f2 + csqrt (of_real f2v) in
   map Re (remdups (map (\<lambda>rt. rt - ce3 / rt) (all_croots 3 u))))" 
  by sorry

lemma solve_depressed_cubic_real: "y \<in> set (solve_depressed_cubic_real e f) 
  \<longleftrightarrow> (y^3 + e * y + f = 0)" 
  by sorry

text \<open>Combining the various algorithms\<close>

lemma degree3_coeffs: "degree p = 3 \<Longrightarrow>
  \<exists> a b c d. p = [: d, c, b, a :] \<and> a \<noteq> 0"
  by sorry

definition roots3_generic :: "('a :: field_char_0 \<Rightarrow> 'a \<Rightarrow> 'a list) \<Rightarrow> 'a poly \<Rightarrow> 'a list" where
  "roots3_generic depressed_solver p = (let 
     cs = coeffs p; 
     a = cs ! 3; b = cs ! 2; c = cs ! 1; d = cs ! 0;
     a3 = 3 * a;
     ba3 = b / a3;
     b2 = b * b;
     b3 = b2 * b;
     e = (c - b2 / a3) / a;
     f = (d + 2 * b3 / (27 * a^2) - b * c / a3) / a;
     roots = depressed_solver e f
     in map (\<lambda> y. y - ba3) roots)" 

lemma roots3_generic: assumes deg: "degree p = 3" 
  and solver: "\<And> e f y. y \<in> set (depressed_solver e f) \<longleftrightarrow> y^3 + e * y + f = 0" 
  shows "set (roots3_generic depressed_solver p) = {x. poly p x = 0}" 
  by sorry

definition croots3 :: "complex poly \<Rightarrow> complex list" where
  "croots3 = roots3_generic solve_depressed_cubic_complex"

lemma croots3: assumes deg: "degree p = 3" 
  shows "set (croots3 p) = { x. poly p x = 0}" 
  by sorry

definition rroots3 :: "real poly \<Rightarrow> real list" where
  "rroots3 = roots3_generic solve_depressed_cubic_real"

lemma rroots3: assumes deg: "degree p = 3" 
  shows "set (rroots3 p) = { x. poly p x = 0}" 
  by sorry

end