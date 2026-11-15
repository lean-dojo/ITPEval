(*
  Statement-only formalization of Hundred Theorems artifact
  hundred-theorems__hol4__087, cataloged as "Desargues's Theorem": two
  projective triangles perspective from a point have collinear intersections
  of corresponding sides, under the source nondegeneracy conditions. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory realTheory;

val desargues_s_theorem =
  ``let x = \P : (real # real) # real. FST (FST P) in
    let y = \P : (real # real) # real. SND (FST P) in
    let z = \P : (real # real) # real. SND P in
    let nonzero =
      \P : (real # real) # real.
        ~(x P = 0 /\ y P = 0 /\ z P = 0)
    in
    let collinear =
      \P Q R : (real # real) # real.
        x P * (y Q * z R - z Q * y R) -
        y P * (x Q * z R - z Q * x R) +
        z P * (x Q * y R - y Q * x R) = 0
    in
      !A B C A1 B1 C1 P Q R S : (real # real) # real.
        nonzero A /\ nonzero B /\ nonzero C /\
        nonzero A1 /\ nonzero B1 /\ nonzero C1 /\
        nonzero P /\ nonzero Q /\ nonzero R /\ nonzero S /\
        ~collinear A1 B S /\
        ~collinear A P C /\
        ~collinear A P R /\
        ~collinear A C B /\
        ~collinear A B R /\
        ~collinear C1 P A1 /\
        ~collinear C1 P B /\
        ~collinear C1 P B1 /\
        ~collinear C1 A1 S /\
        ~collinear C1 A1 B1 /\
        ~collinear P C A1 /\
        ~collinear P C B /\
        ~collinear P A1 R /\
        ~collinear P B Q /\
        ~collinear P Q B1 /\
        ~collinear C B S /\
        ~collinear A1 Q B1
        ==>
        collinear P A1 A /\
        collinear P B B1 /\
        collinear P C1 C /\
        collinear B C Q /\
        collinear B1 C1 Q /\
        collinear A R C /\
        collinear A1 C1 R /\
        collinear B S A /\
        collinear A1 S B1
        ==>
        collinear Q S R``;
