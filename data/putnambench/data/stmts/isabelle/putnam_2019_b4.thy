theory putnam_2019_b4 imports
Complex_Main
"HOL-Analysis.Derivative"
begin

(* note: boosts the domain of f to the entire 2D plane *)
definition putnam_2019_b4_solution :: real where
  "putnam_2019_b4_solution \<equiv> 2 * ln 2 - 1 / 2"
(* 2 * ln 2 - 1 / 2 *)
theorem putnam_2019_b4:
  fixes f :: "real \<Rightarrow> real \<Rightarrow> real"
  and fx fy fxx fxy fyx fyy :: "real \<Rightarrow> real \<Rightarrow> real"
  and Q :: "(real \<times> real) set"
  defines "Q \<equiv> {p. fst p \<ge> 1 \<and> snd p \<ge> 1}"
  and "fx \<equiv> \<lambda>x y. deriv (\<lambda>u. f u y) x"
  and "fy \<equiv> \<lambda>x y. deriv (f x) y"
  and "fxx \<equiv> \<lambda>x y. deriv (\<lambda>u. fx u y) x"
  and "fxy \<equiv> \<lambda>x y. deriv (fx x) y"
  and "fyx \<equiv> \<lambda>x y. deriv (\<lambda>u. fy u y) x"
  and "fyy \<equiv> \<lambda>x y. deriv (fy x) y"
  assumes fdiff:
    "(\<forall>y\<ge>1.
       (\<lambda>x. f x y) differentiable_on {1..} \<and>
       (\<lambda>x. fx x y) differentiable_on {1..} \<and>
       (\<lambda>x. fy x y) differentiable_on {1..}) \<and>
     (\<forall>x\<ge>1.
       f x differentiable_on {1..} \<and>
       fx x differentiable_on {1..} \<and>
       fy x differentiable_on {1..})"
  and fcont:
    "continuous_on Q (\<lambda>p. f (fst p) (snd p)) \<and>
     continuous_on Q (\<lambda>p. fx (fst p) (snd p)) \<and>
     continuous_on Q (\<lambda>p. fy (fst p) (snd p)) \<and>
     continuous_on Q (\<lambda>p. fxx (fst p) (snd p)) \<and>
     continuous_on Q (\<lambda>p. fxy (fst p) (snd p)) \<and>
     continuous_on Q (\<lambda>p. fyx (fst p) (snd p)) \<and>
     continuous_on Q (\<lambda>p. fyy (fst p) (snd p))"
  and feq1: "\<forall>x\<ge>1. \<forall>y\<ge>1.
    x * fx x y + y * fy x y = x * y * ln (x * y)"
  and feq2: "\<forall>x\<ge>1. \<forall>y\<ge>1.
    x^2 * fxx x y + y^2 * fyy x y = x * y"
  shows "Inf {m :: real. \<exists>s\<ge>1.
    m = f (s + 1) (s + 1) - f (s + 1) s - f s (s + 1) + f s s}
      = putnam_2019_b4_solution"
  sorry

end
