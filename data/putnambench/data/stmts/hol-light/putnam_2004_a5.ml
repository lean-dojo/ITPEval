(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2004_a5:
  the expected number of connected monochromatic regions in a uniformly
  two-colored finite rectangular checkerboard is greater than one eighth of
  its number of squares. This file contains no proof.
*)

let statement =
  `!m n:num.
     0 < m * n
     ==>
     let board =
       {p:num#num | FST p < m /\ SND p < n} in
     let adjacent =
       \p q:num#num.
         (FST p = FST q /\
          (SND p + 1 = SND q \/ SND q + 1 = SND p)) \/
         (SND p = SND q /\
          (FST p + 1 = FST q \/ FST q + 1 = FST p)) in
     let connected =
       \(C:(num#num)->bool) (P:num#num) (Q:num#num).
         ?s:(num#num)list.
           ~(s = []) /\
           HD s = P /\
           LAST s = Q /\
           (!k:num.
              k < LENGTH s
              ==> EL k s IN board /\ C (EL k s) = C P) /\
           (!k:num.
              k + 1 < LENGTH s
              ==> adjacent (EL k s) (EL (k + 1) s)) in
     let regions =
       \C:(num#num)->bool.
         {R:(num#num)->bool |
            ?P:num#num.
              P IN board /\
              P IN R /\
              R = {Q:num#num | Q IN board /\ connected C P Q}} in
     let cmr =
       \C:(num#num)->bool. CARD (regions C) in
     let colorings =
       {C:(num#num)->bool |
          !p:num#num. ~(p IN board) ==> ~(C p)} in
     (&(nsum colorings cmr):real) >
     &(2 EXP (m * n)) * (&(m * n) / &8)`;;
