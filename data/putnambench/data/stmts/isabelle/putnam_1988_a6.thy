theory putnam_1988_a6 imports
Complex_Main
"HOL-Algebra.Ring"
"HOL-Analysis.Finite_Cartesian_Product"
begin

definition putnam_1988_a6_solution :: bool where
"putnam_1988_a6_solution \<equiv> True"
theorem putnam_1988_a6:
  shows "(\<forall> (F :: ('a,'m) ring_scheme) (V :: ('b,'n) ring_scheme) (scale :: 'a \<Rightarrow> 'b \<Rightarrow> 'b) (A :: 'b \<Rightarrow> 'b) (n :: nat). 
          n > 0 \<and> field F \<and> abelian_group V \<and>
          (\<forall> a \<in> carrier F. \<forall> b \<in> carrier F. \<forall> x \<in> carrier V. \<forall> y \<in> carrier V.
          scale a x \<in> carrier V \<and> A x \<in> carrier V \<and>
          scale a (x \<oplus>\<^bsub>V\<^esub> y) = scale a x \<oplus>\<^bsub>V\<^esub> scale a y \<and> scale (a \<oplus>\<^bsub>F\<^esub> b) x = scale a x \<oplus>\<^bsub>V\<^esub> scale b x \<and> 
          scale a (scale b x) = scale (a \<otimes>\<^bsub>F\<^esub> b) x \<and> scale \<one>\<^bsub>F\<^esub> x = x \<and> 
          A (scale a x \<oplus>\<^bsub>V\<^esub> scale b y) = scale a (A x) \<oplus>\<^bsub>V\<^esub> scale b (A y)) \<and>
          (\<exists> basis :: 'b list.
          set basis \<subseteq> carrier V \<and> length basis = n \<and> card (set basis) = n \<and>
          (\<forall> coeffs :: 'a list. set coeffs \<subseteq> carrier F \<and> length coeffs = n \<and>
          (\<Oplus>\<^bsub>V\<^esub> i \<in> {0..<n}. scale (coeffs!i) (basis!i)) = \<zero>\<^bsub>V\<^esub>
          \<longrightarrow> (\<forall> i \<in> {0..<n}. coeffs!i = \<zero>\<^bsub>F\<^esub>)) \<and>
          (\<forall> x \<in> carrier V. \<exists> coeffs :: 'a list.
          set coeffs \<subseteq> carrier F \<and> length coeffs = n \<and>
          x = (\<Oplus>\<^bsub>V\<^esub> i \<in> {0..<n}. scale (coeffs!i) (basis!i)))) \<and>
          (\<exists> evecs \<subseteq> ((carrier V) - {\<zero>\<^bsub>V\<^esub>}). card evecs = n + 1 \<and> (\<forall> evec \<in> evecs. \<exists> a \<in> carrier F. A evec = scale a evec) \<and>
          (\<forall> sevecs :: 'b list. set sevecs \<subseteq> evecs \<and> length sevecs = n \<and> card (set sevecs) = n \<longrightarrow>
          (\<forall> coeffs :: 'a list. set coeffs \<subseteq> carrier F \<and> length coeffs = n \<and> 
          (\<Oplus>\<^bsub>V\<^esub> i \<in> {0..<n}. scale (coeffs!i) (sevecs!i)) = \<zero>\<^bsub>V\<^esub> \<longrightarrow> (\<forall> i \<in> {0..<n}. coeffs!i = \<zero>\<^bsub>F\<^esub>))))
          \<longrightarrow> (\<exists> a \<in> carrier F. \<forall> x \<in> carrier V. A x = scale a x))
          \<longleftrightarrow> putnam_1988_a6_solution"
  sorry

end
