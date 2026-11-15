(* Statement-only formalization of PutnamBench corpus artifact putnam_2015_a1:
   a maximum-area triangle inscribed in the positive branch of the hyperbola
   xy = 1 determines two equal areas between the hyperbola and its adjacent
   chords; this file contains no proof. *)

From Stdlib Require Import Reals.

Open Scope R_scope.

Definition putnam_2015_a1_point := (R * R)%type.

Definition putnam_2015_a1_hyperbola
    (p : putnam_2015_a1_point) : Prop :=
  snd p = 1 / fst p /\ 0 < fst p.

Definition putnam_2015_a1_chord
    (p q : putnam_2015_a1_point) (x : R) : R :=
  (snd q - snd p) / (fst q - fst p) * (x - fst p) + snd p.

Definition putnam_2015_a1_triangle_area
    (a b c : putnam_2015_a1_point) : R :=
  Rabs
    ((fst b - fst a) * (snd c - snd a) -
     (snd b - snd a) * (fst c - fst a)) / 2.

Definition putnam_2015_a1_same_integral
    (f : R -> R) (a b : R)
    (g : R -> R) (c d : R) : Prop :=
  exists f_integrable : Riemann_integrable f a b,
    exists g_integrable : Riemann_integrable g c d,
      RiemannInt f_integrable = RiemannInt g_integrable.

Theorem putnam_2015_a1
    (A B P : putnam_2015_a1_point)
    (hAB :
      putnam_2015_a1_hyperbola A /\
      putnam_2015_a1_hyperbola B /\
      fst A < fst B)
    (hP :
      putnam_2015_a1_hyperbola P /\
      fst A < fst P /\
      fst P < fst B /\
      (forall P' : putnam_2015_a1_point,
        putnam_2015_a1_hyperbola P' /\
        fst A < fst P' /\
        fst P' < fst B ->
        putnam_2015_a1_triangle_area A P' B <=
        putnam_2015_a1_triangle_area A P B)) :
  putnam_2015_a1_same_integral
    (fun x : R => putnam_2015_a1_chord A P x - 1 / x)
    (fst A) (fst P)
    (fun x : R => putnam_2015_a1_chord P B x - 1 / x)
    (fst P) (fst B).
Admitted.
