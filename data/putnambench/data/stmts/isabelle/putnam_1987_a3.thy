(*
  Statement-only formalization of PutnamBench artifact putnam_1987_a3,
  concerning positivity implications for solutions of a second-order
  differential equation. This file contains no proof.
*)

theory putnam_1987_a3
  imports Complex_Main
begin

definition putnam_1987_a3_solution :: "bool \<times> bool" where
  "putnam_1987_a3_solution = (False, True)"

definition putnam_1987_a3_deriv ::
    "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real" where
  "putnam_1987_a3_deriv f x =
    (THE d. (f has_real_derivative d) (at x))"

definition putnam_1987_a3_ex_deriv ::
    "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool" where
  "putnam_1987_a3_ex_deriv f x \<longleftrightarrow>
    (\<exists>d. (f has_real_derivative d) (at x))"

theorem putnam_1987_a3:
  shows
    "((\<forall>f :: real \<Rightarrow> real.
        (\<forall>x :: real.
          putnam_1987_a3_ex_deriv f x \<and>
          putnam_1987_a3_ex_deriv (putnam_1987_a3_deriv f) x \<and>
          putnam_1987_a3_deriv (putnam_1987_a3_deriv f) x -
            2 * putnam_1987_a3_deriv f x + f x = 2 * exp x \<and>
          f x > 0) \<longrightarrow>
        (\<forall>x :: real. putnam_1987_a3_deriv f x > 0))
      \<longleftrightarrow> fst putnam_1987_a3_solution) \<and>
     ((\<forall>g :: real \<Rightarrow> real.
        (\<forall>x :: real.
          putnam_1987_a3_ex_deriv g x \<and>
          putnam_1987_a3_ex_deriv (putnam_1987_a3_deriv g) x \<and>
          putnam_1987_a3_deriv (putnam_1987_a3_deriv g) x -
            2 * putnam_1987_a3_deriv g x + g x = 2 * exp x \<and>
          putnam_1987_a3_deriv g x > 0) \<longrightarrow>
        (\<forall>x :: real. g x > 0))
      \<longleftrightarrow> snd putnam_1987_a3_solution)"
  sorry

end
