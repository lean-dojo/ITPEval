(*
  Statement-only formalization of PutnamBench artifact putnam_2019_a4,
  concerning whether vanishing surface integrals over every unit sphere force
  a continuous real-valued function on real three-space to vanish identically.
  The answer is negative. This file contains no proof.
*)

theory putnam_2019_a4
  imports Complex_Main
begin

type_synonym putnam_2019_a4_point = "real \<times> real \<times> real"

definition putnam_2019_a4_sphere_point ::
    "putnam_2019_a4_point \<Rightarrow> real \<Rightarrow> real \<Rightarrow>
      putnam_2019_a4_point" where
  "putnam_2019_a4_sphere_point C theta phi =
    (fst C + sin phi * cos theta,
      fst (snd C) + sin phi * sin theta,
      snd (snd C) + cos phi)"

definition putnam_2019_a4_surface_integral ::
    "(putnam_2019_a4_point \<Rightarrow> real) \<Rightarrow>
      putnam_2019_a4_point \<Rightarrow> real" where
  "putnam_2019_a4_surface_integral f C =
    lim (\<lambda>n::nat.
      let N = real (Suc n);
          dtheta = 2 * pi / N;
          dphi = pi / N
      in dtheta * dphi *
        (\<Sum>i<Suc n. \<Sum>j<Suc n.
          f (putnam_2019_a4_sphere_point C
            ((real i + 1 / 2) * dtheta)
            ((real j + 1 / 2) * dphi)) *
          sin ((real j + 1 / 2) * dphi)))"

theorem putnam_2019_a4:
  shows "\<not> (\<forall>f::putnam_2019_a4_point \<Rightarrow> real.
    continuous_on UNIV f \<longrightarrow>
    (\<forall>C. putnam_2019_a4_surface_integral f C = 0) \<longrightarrow>
    f = (\<lambda>_::putnam_2019_a4_point. 0))"
  oops

end
