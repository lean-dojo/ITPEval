(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2025_b1
  (putnambench__isabelle__putnam_2025_b1): a two-coloring of the real plane
  closed under circumcenters of monochromatic noncollinear triples must be
  constant. This file contains no proof.
*)

theory putnam_2025_b1
  imports Complex_Main
begin

type_synonym putnam_2025_b1_point = "real \<times> real"

definition putnam_2025_b1_sqdist ::
    "putnam_2025_b1_point \<Rightarrow> putnam_2025_b1_point \<Rightarrow> real" where
  "putnam_2025_b1_sqdist P Q =
    (fst P - fst Q)^2 + (snd P - snd Q)^2"

definition putnam_2025_b1_noncollinear ::
    "putnam_2025_b1_point \<Rightarrow> putnam_2025_b1_point \<Rightarrow>
      putnam_2025_b1_point \<Rightarrow> bool" where
  "putnam_2025_b1_noncollinear A B C \<longleftrightarrow>
    (fst B - fst A) * (snd C - snd A) \<noteq>
      (snd B - snd A) * (fst C - fst A)"

definition putnam_2025_b1_same_color ::
    "(putnam_2025_b1_point \<Rightarrow> bool) \<Rightarrow>
      putnam_2025_b1_point \<Rightarrow> putnam_2025_b1_point \<Rightarrow>
      putnam_2025_b1_point \<Rightarrow> bool" where
  "putnam_2025_b1_same_color color A B C \<longleftrightarrow>
    color A = color B \<and> color A = color C"

definition putnam_2025_b1_is_circumcenter ::
    "putnam_2025_b1_point \<Rightarrow> putnam_2025_b1_point \<Rightarrow>
      putnam_2025_b1_point \<Rightarrow> putnam_2025_b1_point \<Rightarrow> bool" where
  "putnam_2025_b1_is_circumcenter U A B C \<longleftrightarrow>
    putnam_2025_b1_sqdist U A = putnam_2025_b1_sqdist U B \<and>
    putnam_2025_b1_sqdist U A = putnam_2025_b1_sqdist U C"

theorem putnam_2025_b1:
  fixes color :: "putnam_2025_b1_point \<Rightarrow> bool"
  assumes h:
    "\<forall>A B C U :: putnam_2025_b1_point.
      putnam_2025_b1_noncollinear A B C \<longrightarrow>
      putnam_2025_b1_same_color color A B C \<longrightarrow>
      putnam_2025_b1_is_circumcenter U A B C \<longrightarrow>
      color U = color A"
  shows "\<exists>c :: bool. \<forall>P :: putnam_2025_b1_point. color P = c"
  sorry

end
