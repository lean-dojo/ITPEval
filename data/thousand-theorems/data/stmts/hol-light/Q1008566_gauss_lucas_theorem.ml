(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1008566
  (thousand-theorems__hol-light__Q1008566), "Gauss–Lucas theorem": the
  critical points of a nonconstant complex polynomial lie in the convex hull
  of its roots, together with the explicit root-multiplicity-weighted
  center-of-mass identity. This file contains no proof.
*)

let cpoly_output = open_out "/dev/null";;
let cpoly_formatter = Format.formatter_of_out_channel cpoly_output;;
let previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file cpoly_formatter path);;
let cpoly_loaded =
  Toploop.use_file cpoly_formatter "Complex/cpoly.ml";;
Hol_loader.file_loader := previous_file_loader;;
Format.pp_print_flush cpoly_formatter ();;
close_out cpoly_output;;
if not cpoly_loaded then failwith "failed to load Complex/cpoly.ml";;

let Polynomial_eq_centerMass_of_eval_derivative_eq_zero =
  `let root_set =
     \p:complex list. {w:complex | poly p w = Cx(&0)} in
   let deriv_root_weight =
     \(p:complex list) (z:complex) (w:complex).
       if poly p z = Cx(&0) then
         if w = z then &1 else &0
       else
         &(order w p) / (norm(z - w) pow 2) in
   let complex_sum =
     \(s:complex->bool) (f:complex->complex).
       iterate ((+):complex->complex->complex) s f in
   let center_mass =
     \(s:complex->bool) (weight:complex->real).
       Cx(inv(sum s weight)) *
       complex_sum s (\w:complex. Cx(weight w) * w) in
   !p:complex list. !z:complex.
     0 < degree p /\
     poly (poly_diff p) z = Cx(&0)
     ==>
     z = center_mass (root_set p) (deriv_root_weight p z)`;;

let Polynomial_rootSet_derivative_subset_convexHull_rootSet =
  `let root_set =
     \p:complex list. {w:complex | poly p w = Cx(&0)} in
   let complex_convex =
     \(t:complex->bool).
       !x y:complex. !u v:real.
         x IN t /\ y IN t /\
         &0 <= u /\ &0 <= v /\ u + v = &1
         ==> Cx(u) * x + Cx(v) * y IN t in
   let complex_convex_hull =
     \(s:complex->bool).
       {z:complex |
          !t:complex->bool.
            s SUBSET t /\ complex_convex t ==> z IN t} in
   !p:complex list.
     0 < degree p
     ==>
     root_set (poly_diff p) SUBSET
     complex_convex_hull (root_set p)`;;
