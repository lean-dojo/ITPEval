(*
  Statement-only formalization of PutnamBench artifact putnam_1966_a5:
  a linear operator on continuous real-valued functions that preserves
  equality on closed intervals is pointwise multiplication by a continuous
  function. This file contains no proof.
*)

let statement =
  `let continuous =
     \(f:real->real).
       !x e:real.
         &0 < e
         ==> ?d:real.
               &0 < d /\
               !y:real. abs (y - x) < d ==> abs (f y - f x) < e in
   !op:(real->real)->(real->real).
     (!f:real->real. continuous f ==> continuous (op f)) /\
     (!a b:real. !f g:real->real.
        continuous f /\ continuous g
        ==> op (\x:real. a * f x + b * g x) =
            (\x:real. a * op f x + b * op g x)) /\
     (!r s:real.
        r <= s
        ==> !f g:real->real.
              continuous f /\ continuous g /\
              (!x:real. r <= x /\ x <= s ==> f x = g x)
              ==> !x:real. r <= x /\ x <= s
                           ==> op f x = op g x)
     ==> ?f:real->real.
           continuous f /\
           !g:real->real.
             continuous g
             ==> op g = (\x:real. f x * g x)`;;
