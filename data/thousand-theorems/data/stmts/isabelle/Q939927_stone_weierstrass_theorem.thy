(*
  Statement-only formalization of the thousand-theorems corpus artifact Q939927,
  "Stone-Weierstrass theorem": a point-separating real subalgebra of continuous
  functions on a compact space is uniformly dense. This file contains no proof.
*)

theory Q939927_stone_weierstrass_theorem
  imports "HOL-Analysis.Weierstrass_Theorems"
begin

theorem q939927_stone_weierstrass_theorem:
  fixes K :: "'a::topological_space set"
    and A :: "('a \<Rightarrow> real) set"
  assumes compact_carrier: "compact K"
    and continuous_members: "\<And>g. g \<in> A \<Longrightarrow> continuous_on K g"
    and constants:
      "\<And>c::real. \<exists>g\<in>A. \<forall>x\<in>K. g x = c"
    and subtraction_closed:
      "\<And>g h. g \<in> A \<Longrightarrow> h \<in> A \<Longrightarrow>
        \<exists>k\<in>A. \<forall>x\<in>K. k x = g x - h x"
    and multiplication_closed:
      "\<And>g h. g \<in> A \<Longrightarrow> h \<in> A \<Longrightarrow>
        \<exists>k\<in>A. \<forall>x\<in>K. k x = g x * h x"
    and separates_points:
      "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow> x \<noteq> y \<Longrightarrow>
        \<exists>g\<in>A. g x \<noteq> g y"
  shows "\<forall>f. continuous_on K f \<longrightarrow>
    (\<forall>e>0. \<exists>g\<in>A. \<forall>x\<in>K. \<bar>g x - f x\<bar> < e)"
  sorry

end
