(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1032886
  (thousand-theorems__hol-light__Q1032886), "Hales–Jewett theorem": for every
  finite alphabet and finite color set, some finite-dimensional word space
  has a nondegenerate monochromatic combinatorial line under every coloring.
  This file contains no proof.
*)

let Q1032886_HALES_JEWETT_THEOREM =
  `let valid_word =
     \(alphabet:A->bool) (n:num) (w:A list).
       LENGTH w = n /\
       (!x:A. MEM x w ==> x IN alphabet) in
   let valid_line =
     \(alphabet:A->bool) (n:num) (pattern:(A option)list).
       LENGTH pattern = n /\
       MEM NONE pattern /\
       (!a:A. MEM (SOME a) pattern ==> a IN alphabet) in
   let line_word =
     \(pattern:(A option)list) (x:A).
       MAP
         (\entry:A option.
            if entry = NONE then x
            else @a:A. entry = SOME a)
         pattern in
   !alphabet:A->bool. !colors:B->bool.
     FINITE alphabet /\ FINITE colors
     ==> ?n:num.
           !C:A list->B.
             (!w:A list.
                valid_word alphabet n w
                ==> C w IN colors)
             ==> ?pattern:(A option)list.
                   ?c:B.
                     valid_line alphabet n pattern /\
                     c IN colors /\
                     !x:A.
                       x IN alphabet
                       ==> C (line_word pattern x) = c`;;
