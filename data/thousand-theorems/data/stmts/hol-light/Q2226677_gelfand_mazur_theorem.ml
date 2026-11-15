(*
  Statement-only formalization of Thousand Theorems corpus artifact Q2226677,
  "Gelfand–Mazur theorem": the canonical complex scalar embedding into a
  complete complex normed division algebra is an algebra isomorphism. This
  file contains no proof.
*)

let q2226677_output = open_out "/dev/null";;
let q2226677_formatter =
  Format.formatter_of_out_channel q2226677_output;;
let q2226677_previous_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file q2226677_formatter path);;
let q2226677_loaded =
  Toploop.use_file q2226677_formatter "Complex/complexnumbers.ml";;
Hol_loader.file_loader := q2226677_previous_loader;;
Format.pp_print_flush q2226677_formatter ();;
close_out q2226677_output;;
if not q2226677_loaded then failwith "Unable to load complex library";;

let Q2226677_GELFAND_MAZUR_THEOREM =
 `let normed_ring =
    \(zero:A) (oneA:A) (add:A->A->A) (mul:A->A->A)
     (neg:A->A) (normA:A->real).
       (!x y z:A. add x (add y z) = add (add x y) z) /\
       (!x y:A. add x y = add y x) /\
       (!x:A. add zero x = x) /\
       (!x:A. add (neg x) x = zero) /\
       (!x y z:A. mul x (mul y z) = mul (mul x y) z) /\
       (!x:A. mul oneA x = x /\ mul x oneA = x) /\
       (!x y z:A.
          mul x (add y z) = add (mul x y) (mul x z)) /\
       (!x y z:A.
          mul (add x y) z = add (mul x z) (mul y z)) /\
       normA zero = &0 /\
       (!x:A. &0 <= normA x) /\
       (!x:A. normA x = &0 <=> x = zero) /\
       (!x:A. normA (neg x) = normA x) /\
       (!x y:A. normA (add x y) <= normA x + normA y) /\
       (!x y:A. normA (mul x y) <= normA x * normA y) in
  let complex_normed_algebra =
    \(zero:A) (oneA:A) (add:A->A->A) (mul:A->A->A)
     (normA:A->real) (algebra_map:complex->A).
       algebra_map (Cx(&0)) = zero /\
       algebra_map (Cx(&1)) = oneA /\
       (!z w:complex.
          algebra_map (z + w) = add (algebra_map z) (algebra_map w)) /\
       (!z w:complex.
          algebra_map (z * w) = mul (algebra_map z) (algebra_map w)) /\
       (!z:complex. !x:A.
          mul (algebra_map z) x = mul x (algebra_map z)) /\
       (!z:complex. !x:A.
          normA (mul (algebra_map z) x) <= norm z * normA x) in
  let tends_to =
    \(add:A->A->A) (neg:A->A) (normA:A->real)
     (u:num->A) (x:A).
       !epsilon:real.
         &0 < epsilon
         ==> ?N:num. !n:num.
               N <= n
               ==> normA (add (u n) (neg x)) < epsilon in
  let complete_space =
    \(add:A->A->A) (neg:A->A) (normA:A->real).
       !u:num->A.
         (!epsilon:real.
            &0 < epsilon
            ==> ?N:num. !m n:num.
                  N <= m /\ N <= n
                  ==> normA (add (u m) (neg (u n))) < epsilon)
         ==> ?x:A. tends_to add neg normA u x in
  let is_unit =
    \(oneA:A) (mul:A->A->A) (x:A).
       ?y:A. mul x y = oneA /\ mul y x = oneA in
  !zero oneA:A.
  !add mul:A->A->A.
  !neg:A->A.
  !normA:A->real.
  !algebra_map:complex->A.
    normed_ring zero oneA add mul neg normA /\
    complex_normed_algebra zero oneA add mul normA algebra_map /\
    complete_space add neg normA /\
    (!x:A. is_unit oneA mul x <=> ~(x = zero))
    ==> ?inverse:A->complex.
          (!z:complex. inverse (algebra_map z) = z) /\
          (!x:A. algebra_map (inverse x) = x)`;;
