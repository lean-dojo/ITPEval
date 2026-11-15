theory putnam_2014_a4 imports
Complex_Main
begin

definition putnam_2014_a4_solution :: real where
  "putnam_2014_a4_solution \<equiv> 1 / 3"
(* 1 / 3 *)
theorem putnam_2014_a4:
  fixes Xrandvar :: "(nat \<Rightarrow> real) \<Rightarrow> bool"
  and E :: "(nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> real"
  defines "Xrandvar \<equiv> \<lambda>X :: nat \<Rightarrow> real.
    (\<forall>n. X n \<in> {0 .. 1}) \<and> summable X \<and> suminf X = 1"
  and "E \<equiv> \<lambda>(X :: nat \<Rightarrow> real) (f :: nat \<Rightarrow> real).
    suminf (\<lambda>n. f n * X n)"
  shows "Inf {X0 :: real. \<exists>X :: nat \<Rightarrow> real.
    Xrandvar X \<and>
    summable (\<lambda>n. real n * X n) \<and>
    summable (\<lambda>n. (real n)^2 * X n) \<and>
    summable (\<lambda>n. (real n)^3 * X n) \<and>
    E X (\<lambda>n. real n) = 1 \<and>
    E X (\<lambda>n. (real n)^2) = 2 \<and>
    E X (\<lambda>n. (real n)^3) = 5 \<and>
    X0 = X 0} = putnam_2014_a4_solution"
  sorry

end
