theory putnam_2018_b5 imports
Complex_Main
"HOL-Analysis.Finite_Cartesian_Product"
"HOL-Analysis.Derivative"
begin

theorem putnam_2018_b5:
  fixes f :: "real \<Rightarrow> real \<Rightarrow> real^2"
  and f11 f12 f21 f22 :: "real \<Rightarrow> real \<Rightarrow> real"
  defines "f11 \<equiv> \<lambda>x2 x1. (f x1 x2)$0"
  and "f12 \<equiv> \<lambda>x1 x2. (f x1 x2)$0"
  and "f21 \<equiv> \<lambda>x2 x1. (f x1 x2)$1"
  and "f22 \<equiv> \<lambda>x1 x2. (f x1 x2)$1"
  assumes fdiff: "\<forall>x::real.
    f11 x differentiable_on UNIV \<and>
    f12 x differentiable_on UNIV \<and>
    f21 x differentiable_on UNIV \<and>
    f22 x differentiable_on UNIV"
  and fderivcont:
    "continuous_on UNIV (\<lambda>p::real\<times>real. deriv (f11 (snd p)) (fst p)) \<and>
     continuous_on UNIV (\<lambda>p::real\<times>real. deriv (f12 (fst p)) (snd p)) \<and>
     continuous_on UNIV (\<lambda>p::real\<times>real. deriv (f21 (snd p)) (fst p)) \<and>
     continuous_on UNIV (\<lambda>p::real\<times>real. deriv (f22 (fst p)) (snd p))"
  and fpos: "\<forall>x1 x2 :: real.
    deriv (f11 x2) x1 > 0 \<and>
    deriv (f12 x1) x2 > 0 \<and>
    deriv (f21 x2) x1 > 0 \<and>
    deriv (f22 x1) x2 > 0"
  and fexprgrt0: "\<forall>x1 x2 :: real.
    deriv (f11 x2) x1 * deriv (f22 x1) x2 -
      (1 / 4) * (deriv (f12 x1) x2 + deriv (f21 x2) x1)^2 > 0"
  shows "inj (\<lambda>(a, b). f a b)"
  sorry

end
