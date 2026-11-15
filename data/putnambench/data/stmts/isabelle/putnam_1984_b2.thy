theory putnam_1984_b2 imports Complex_Main
begin

definition putnam_1984_b2_solution :: "real" where
"putnam_1984_b2_solution \<equiv> 8"
theorem putnam_1984_b2:
  fixes f :: "real \<Rightarrow> real \<Rightarrow> real"
  defines "f \<equiv> \<lambda> u v :: real. (u - v)^2 + (sqrt (2 - u^2) - 9/v)^2"
  shows "(\<forall> u \<in> {0<..<sqrt 2}. \<forall> v > 0.
      putnam_1984_b2_solution \<le> f u v) \<and>
    (\<exists> u \<in> {0<..<sqrt 2}. \<exists> v > 0.
      f u v = putnam_1984_b2_solution)"
  sorry

end
