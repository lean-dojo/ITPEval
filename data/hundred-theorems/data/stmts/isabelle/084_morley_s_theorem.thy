theory Morley 


imports Complex_Axial_Symmetry 

begin

section \<open>Rotations\<close>

locale complex_rotation =
  fixes A::complex and \<theta>::real
begin

definition \<open>r z = A + (z-A)*cis(\<theta>)\<close>

lemma cmod_inv_rotation:\<open>cmod (z-A) = cmod (r z - A)\<close>
  by sorry

lemma inner_ang:\<open>cos (\<angle> z1 z2)*(cmod z1 *cmod z2) = Re (innerprod z1 z2)\<close>
  by sorry

lemma ang_eq_cos_theta:\<open>z\<noteq>A \<Longrightarrow> cos (angle_c z A (r z)) = cos (\<theta>)\<close>
  by sorry

lemma cdist_dist:\<open>cdist = dist\<close>
  by sorry

lemma ang_eq_theta:assumes h:\<open>z\<noteq>A\<close> shows \<open>angle_c z A (r z) = \<downharpoonright>\<theta>\<downharpoonleft>\<close>
  by sorry

lemma inj_r:\<open>inj r\<close>
  by sorry

lemma img_eqI:\<open>cdist A z1 = cdist A z2 \<and> angle_c z1 A z2 = \<theta> \<Longrightarrow> z2 = r z1\<close>
  by sorry

lemma r_id_iff:\<open>\<downharpoonright>\<theta>\<downharpoonleft> = 0 \<longleftrightarrow> r = id\<close>
  by sorry

end


lemma axial_symmetry_eq:\<open>axial_symmetry B C P = axial_symmetry C B P\<close> if \<open>C\<noteq>B\<close> for C B P
  by sorry

lemma img_r_sym:
  assumes h:\<open>z1 \<noteq> z2\<close> \<open>z \<notin> line z1 z2\<close>
  shows \<open>axial_symmetry z1 z2 z = complex_rotation.r z1 (\<downharpoonright>2*angle_c z z1 z2\<downharpoonleft>) z\<close>
  by sorry

lemma img_r_sym':
  assumes h:\<open>z1 \<noteq> z2\<close> \<open>z\<notin>line z1 z2\<close>
  shows \<open>axial_symmetry z1 z2 z = complex_rotation.r z1 (\<downharpoonright>-2*angle_c z2 z1 z\<downharpoonleft>) z\<close>
  by sorry

lemma equality_for_pqr:
  assumes 1:\<open>(a2::complex)*a3\<noteq>1\<close> and 2:\<open>\<And>z. h z = a3*z + b3\<close> and 3:\<open>\<And>z. g z = a2*z + b2\<close> and 4:\<open>g (h z) = z\<close>
  shows \<open>z = (a2*b3 + b2)/(1-a2*a3)\<close>
  by sorry

lemma equality_for_comp:
  assumes 2:\<open>\<And>z. h z = (a3::complex)*z + b3\<close> and 3:\<open>\<And>z. g z = a2*z + b2\<close> 
    and 4:\<open>\<And>z. f z = a1*z +b1\<close> 
  shows \<open>((f\<circ>f\<circ>f)\<circ>(g\<circ>g\<circ>g)\<circ>(h\<circ>h\<circ>h)) z = (a1*a2*a3)^3*z +(a1^2+a1+1)*b1 +a1^3*(a2^2+a2+1)*b2 
+a1^3*a2^3*(a3^2+a3+1)*b3 \<close>
  by sorry

lemma eq_translation_id:
  assumes \<open>h = complex_rotation.r A 0\<close> \<open>h B = B\<close>
  shows \<open>h = id\<close>
  by sorry

lemma r_eqI: 
  assumes \<open>A = B\<close> \<open>\<theta>1 = \<theta>2\<close> 
  shows \<open>r A \<theta>1 = r B \<theta>2\<close>
  by sorry

lemma r_eqI': 
  assumes \<open>A = B\<close> \<open>\<theta>1 = \<theta>2\<close> 
  shows \<open>r A \<theta>1 z = r B \<theta>2 z\<close>
  by sorry

lemma composed_rotations_same_center:
  shows \<open>(complex_rotation.r A \<theta>1 \<circ> complex_rotation.r A \<theta>2) = complex_rotation.r A (\<theta>1 + \<theta>2)\<close>
  by sorry


lemma composed_rotations:
  assumes h:\<open>\<downharpoonright>\<theta>1 + \<theta>2\<downharpoonleft> \<noteq> 0\<close>
  shows \<open>(complex_rotation.r A \<theta>1 \<circ> complex_rotation.r B \<theta>2) = 
           complex_rotation.r ((A*(1-cis \<theta>1) + B*cis \<theta>1*(1-cis \<theta>2))/(1-cis (\<theta>1+\<theta>2))) (\<theta>1 + \<theta>2)\<close>
  by sorry


lemma composed_rotation_is_trans:
  assumes \<open>\<downharpoonright>\<theta>1 + \<theta>2\<downharpoonleft> = 0\<close>  
  shows \<open>(complex_rotation.r A \<theta>1 \<circ> complex_rotation.r B \<theta>2) z = z + (B - A)*(cis(\<theta>1) - 1)\<close>
  by sorry

section \<open>Morley's theorem\<close>

text \<open>We begin by proving the Morley's theorem in the case where angles are positives
then using the congruence between two triangles with the same angles only not of the same sign
we prove Morley's theorem when angles are negatives.

We then proceed to conclude because in a triangle either angles are all negatives or all the
angles are positives depending on orientation.\<close>

theorem Morley_pos:
  assumes\<open>\<not>collinear A B C\<close>
    \<open>angle_c A B R = angle_c A B C / 3\<close> (is \<open>?abr = ?abc\<close>)
    "angle_c B A R = angle_c B A C / 3" (is \<open>?bar = ?\<alpha>\<close>)
    "angle_c B C P = angle_c B C A / 3" (is \<open>?bcp = ?bca\<close>)
    "angle_c C B P = angle_c C B A / 3" (is \<open>?cbp = ?\<beta>\<close>)
    "angle_c C A Q = angle_c C A B / 3" (is \<open>?caq = ?cab\<close>)
    "angle_c A C Q = angle_c A C B / 3" (is \<open>?acq = ?\<gamma>\<close>)
    and hhh:\<open>\<downharpoonright>angle_c B A C / 3+angle_c C B A / 3+angle_c A C B / 3\<downharpoonleft> = pi/3\<close>
  shows  \<open>cdist R P = cdist P Q \<and> cdist Q R = cdist P Q\<close>
  by sorry

theorem Morley_neg: 
  assumes\<open>\<not>collinear A B C\<close>
    \<open>angle_c A B R = angle_c A B C / 3\<close> (is \<open>?abr = ?abc\<close>)
    "angle_c B A R = angle_c B A C / 3" (is \<open>?bar = ?\<alpha>\<close>)
    "angle_c B C P = angle_c B C A / 3" (is \<open>?bcp = ?bca\<close>)
    "angle_c C B P = angle_c C B A / 3" (is \<open>?cbp = ?\<beta>\<close>)
    "angle_c C A Q = angle_c C A B / 3" (is \<open>?caq = ?cab\<close>)
    "angle_c A C Q = angle_c A C B / 3" (is \<open>?acq = ?\<gamma>\<close>)
    and hhh:\<open>\<downharpoonright>angle_c B A C / 3+angle_c C B A / 3+angle_c A C B / 3\<downharpoonleft> = -pi/3\<close>
  shows  \<open>cdist R P = cdist P Q \<and> cdist Q R = cdist P Q\<close>
  by sorry

theorem Morley:
  assumes\<open>\<not>collinear A B C\<close>
    \<open>angle_c A B R = angle_c A B C / 3\<close> (is \<open>?abr = ?abc\<close>)
    "angle_c B A R = angle_c B A C / 3" (is \<open>?bar = ?\<alpha>\<close>)
    "angle_c B C P = angle_c B C A / 3" (is \<open>?bcp = ?bca\<close>)
    "angle_c C B P = angle_c C B A / 3" (is \<open>?cbp = ?\<beta>\<close>)
    "angle_c C A Q = angle_c C A B / 3" (is \<open>?caq = ?cab\<close>)
    "angle_c A C Q = angle_c A C B / 3" (is \<open>?acq = ?\<gamma>\<close>)
  shows  \<open>cdist R P = cdist P Q \<and> cdist Q R = cdist P Q\<close>
  by sorry

end