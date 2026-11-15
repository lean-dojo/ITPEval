(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1999_a1:
  existence of three real polynomials whose signed combination of absolute
  values agrees everywhere with a specified piecewise-linear function. This
  file contains no proof.
*)

let statement =
  `let eval =
     \p:real list. \x:real.
       ITLIST (\c acc. c + x * acc) p (&0) in
   let putnam_1999_a1_solution = T in
   putnam_1999_a1_solution <=>
   (?f g h:real list.
      !x:real.
        abs (eval f x) - abs (eval g x) + eval h x =
        if x < --(&1) then --(&1)
        else if x <= &0 then &3 * x + &2
        else --(&2) * x + &2)`;;
