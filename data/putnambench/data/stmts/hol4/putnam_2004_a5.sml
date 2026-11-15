(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2004_a5:
  the expected number of connected monochromatic regions in a uniformly
  two-colored nonempty finite rectangular checkerboard is greater than one
  eighth of the number of squares. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory pairTheory pred_setTheory ratTheory;

val putnam_2004_a5 =
  ``!m n : num.
      0 < m /\ 0 < n
      ==>
      let board =
        {P : num # num | FST P < m /\ SND P < n}
      in
      let adj =
        \P Q : num # num.
          P IN board /\ Q IN board /\
          ((FST P = FST Q /\
            (SND P + 1 = SND Q \/ SND Q + 1 = SND P)) \/
           (SND P = SND Q /\
            (FST P + 1 = FST Q \/ FST Q + 1 = FST P)))
      in
      let connected =
        \C : (num # num) -> bool. \P Q : num # num.
          ?S : (num # num) list.
            S <> [] /\
            HD S = P /\
            LAST S = Q /\
            (!k : num. k < LENGTH S ==> EL k S IN board) /\
            (?c : bool.
               !k : num. k < LENGTH S ==> (C (EL k S) = c)) /\
            (!k : num.
               SUC k < LENGTH S ==> adj (EL k S) (EL (SUC k) S))
      in
      let cmr =
        \C : (num # num) -> bool.
          CARD
            {R : (num # num) set |
               ?P : num # num.
                 P IN board /\
                 R =
                   {Q : num # num |
                      Q IN board /\ connected C P Q}}
      in
      let colorings =
        {C : (num # num) -> bool |
           !P : num # num. P NOTIN board ==> (C P = F)}
      in
        rat_of_num (SIGMA cmr colorings) >
          rat_of_num (2 EXP (m * n)) *
            (rat_of_num (m * n) / 8q)``;
