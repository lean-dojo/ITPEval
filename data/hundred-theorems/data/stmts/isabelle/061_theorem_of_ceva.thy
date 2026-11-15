(*  Author: Mathias Schack Rabing <mathiasrabing@outlook.com> *)

theory Ceva
imports
  Triangle.Triangle
begin

definition\<^marker>\<open>tag important\<close> Triangle_area :: "'a::real_inner \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> real"
  where "Triangle_area x y z = abs(sin (angle x y z)) * dist x y * dist y z"

lemma Triangle_area_per1 : "Triangle_area a b c = Triangle_area b c a"
  by sorry

lemma Triangle_area_per2 : "Triangle_area a b c = Triangle_area b a c"
  by sorry

lemma collinear_angle: 
  fixes a b c :: "'a::euclidean_space"
  shows "collinear {a, b, c} \<Longrightarrow> a \<noteq> b \<Longrightarrow> b \<noteq> c \<Longrightarrow> angle a b c \<in> {0, pi}"
  by sorry

lemma Triangle_area_0 : 
  fixes c :: "'a::euclidean_space"
  shows "Triangle_area a b c = 0 \<longleftrightarrow> collinear {a,b,c}"
  by sorry


lemma Angle_longer_side : 
  fixes a :: "'a :: euclidean_space"
  assumes Col : "between (b,d) c"
  assumes NeqBC : "b \<noteq> c"
  shows "angle a b c = angle a b d"
  by sorry

lemma Triangle_area_comb :
  fixes c :: "'a::euclidean_space"
  assumes Col : "between (b,c) m"
  shows "Triangle_area a b m + Triangle_area a c m = Triangle_area a b c"
  by sorry

lemma Triangle_area_cal :
  fixes a :: "'a::euclidean_space"
  assumes Col : "collinear {a,m,b}"
  shows "\<exists> k. dist a m * k = Triangle_area a c m \<and> dist b m * k = Triangle_area b c m"
  by sorry

lemma Triangle_area_comb_alt :
  fixes a :: "'a::euclidean_space"
  assumes Col1 : "collinear {a,m,b}"
  assumes Col2 : "collinear {c,k,m}"
  shows Goal : "\<exists> h. dist a m * h = Triangle_area a c k \<and> dist b m * h = Triangle_area b c k"
  by sorry

lemma Cevas : 
  fixes a :: "'a::euclidean_space"
  assumes MidCol : "collinear {a,k,d} \<and> collinear {b,k,e} \<and> collinear {c,k,f}"
  assumes TriCol : "collinear {a,f,b} \<and> collinear {a,e,c} \<and> collinear {b,d,c}"
  assumes Triangle : "\<not> collinear {a,b,c}"
  shows "dist a f * dist b d * dist c e = dist f b * dist d c * dist e a"
  by sorry


end