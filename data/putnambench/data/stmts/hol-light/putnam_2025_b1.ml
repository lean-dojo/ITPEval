(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2025_b1
  (putnambench__hol-light__putnam_2025_b1): every two-coloring of the real
  plane that preserves the color of monochromatic noncollinear triples at
  their circumcenters is constant. This file contains no proof.
*)

let statement =
  `let squared_distance =
     \(P:real#real) (Q:real#real).
       (FST P - FST Q) pow 2 + (SND P - SND Q) pow 2 in
   let noncollinear =
     \(A:real#real) (B:real#real) (C:real#real).
       ~((FST B - FST A) * (SND C - SND A) =
         (SND B - SND A) * (FST C - FST A)) in
   !color:(real#real)->bool.
     (!A B C O:real#real.
        noncollinear A B C /\
        color A = color B /\
        color A = color C /\
        squared_distance O A = squared_distance O B /\
        squared_distance O A = squared_distance O C
        ==> color O = color A)
     ==> ?c:bool. !P:real#real. color P = c`;;
