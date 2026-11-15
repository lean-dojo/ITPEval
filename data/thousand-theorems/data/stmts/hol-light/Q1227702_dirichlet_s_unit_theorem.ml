(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1227702,
  "Dirichlet's unit theorem": for an arbitrary number field, the units modulo
  torsion have rank one less than the number of infinite places, with a basis
  whose lifts give unique torsion-times-integer-powers decompositions.
  This file contains no proof.
*)

let q1227702_output = open_out "/dev/null";;
let q1227702_formatter = Format.formatter_of_out_channel q1227702_output;;
let q1227702_previous_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file q1227702_formatter path);;
let q1227702_loaded =
  Toploop.use_file q1227702_formatter "Complex/complexnumbers.ml";;
Hol_loader.file_loader := q1227702_previous_loader;;
Format.pp_print_flush q1227702_formatter ();;
close_out q1227702_output;;
if not q1227702_loaded then failwith "Unable to load complex library";;

let Q1227702_DIRICHLET_S_UNIT_THEOREM =
 `let field =
      \(zero:A) (one_value:A) (add:A->A->A) (mul:A->A->A)
       (neg:A->A) (inv:A->A) (of_int:int->A).
        ~(zero = one_value) /\
        (!x y:A. add x y = add y x) /\
        (!x y z:A. add (add x y) z = add x (add y z)) /\
        (!x:A. add x zero = x) /\
        (!x:A. add x (neg x) = zero) /\
        (!x y:A. mul x y = mul y x) /\
        (!x y z:A. mul (mul x y) z = mul x (mul y z)) /\
        (!x:A. mul x one_value = x) /\
        (!x y z:A. mul x (add y z) = add (mul x y) (mul x z)) /\
        (!x:A. ~(x = zero) ==> mul x (inv x) = one_value) /\
        of_int (&0) = zero /\
        of_int (&1) = one_value /\
        (!m n:int. of_int (m + n) = add (of_int m) (of_int n)) /\
        (!m n:int. of_int (m * n) = mul (of_int m) (of_int n)) /\
        (!m:int. of_int (--m) = neg (of_int m)) /\
        (!m n:int. of_int m = of_int n ==> m = n) in
   let rational_element =
      \(mul:A->A->A) (inv:A->A) (of_int:int->A) (q:A).
        ?m:int n:num.
          q = mul (of_int m) (inv (of_int (&(SUC n)))) in
   let finite_sum =
      \(add:A->A->A) (n:num) (f:num->A).
        iterate add {i | i < n} f in
   let finite_product =
      \(mul:A->A->A) (n:num) (f:num->A).
        iterate mul {i | i < n} f in
   let natural_power =
      \(mul:A->A->A) (x:A) (n:num).
        finite_product mul n (\i. x) in
   let integer_power =
      \(mul:A->A->A) (inv:A->A) (x:A) (n:int).
        if &0 <= n
        then natural_power mul x (num_of_int n)
        else inv (natural_power mul x (num_of_int (--n))) in
   let rational_coordinates =
      \(add:A->A->A) (mul:A->A->A) (inv:A->A)
       (of_int:int->A) (dimension:num) (basis:num->A)
       (x:A) (coefficients:num->A).
        (!i. i < dimension
             ==> rational_element mul inv of_int (coefficients i)) /\
        x =
        finite_sum add dimension
          (\i. mul (coefficients i) (basis i)) in
   let number_field =
      \(zero:A) (one_value:A) (add:A->A->A) (mul:A->A->A)
       (neg:A->A) (inv:A->A) (of_int:int->A).
        field zero one_value add mul neg inv of_int /\
        ?dimension basis.
          0 < dimension /\
          (!x:A.
             ?coefficients.
               rational_coordinates add mul inv of_int
                 dimension basis x coefficients) /\
          (!x:A c d.
             rational_coordinates add mul inv of_int
               dimension basis x c /\
             rational_coordinates add mul inv of_int
               dimension basis x d
             ==> !i. i < dimension ==> c i = d i) in
   let integer_element =
      \(of_int:int->A) (x:A). ?m:int. x = of_int m in
   let algebraic_integer =
      \(zero:A) (one_value:A) (add:A->A->A) (mul:A->A->A)
       (of_int:int->A) (x:A).
        ?degree coefficients.
          0 < degree /\
          (!i. i <= degree
               ==> integer_element of_int (coefficients i)) /\
          coefficients degree = one_value /\
          finite_sum add (SUC degree)
            (\i. mul (coefficients i) (natural_power mul x i)) =
          zero in
   let unit =
      \(zero:A) (one_value:A) (add:A->A->A) (mul:A->A->A)
       (inv:A->A) (of_int:int->A) (x:A).
        ~(x = zero) /\
        algebraic_integer zero one_value add mul of_int x /\
        algebraic_integer zero one_value add mul of_int (inv x) in
   let torsion_unit =
      \(zero:A) (one_value:A) (add:A->A->A) (mul:A->A->A)
       (inv:A->A) (of_int:int->A) (x:A).
        unit zero one_value add mul inv of_int x /\
        ?n. 0 < n /\ natural_power mul x n = one_value in
   let field_embedding =
      \(zero:A) (one_value:A) (add:A->A->A) (mul:A->A->A)
       (sigma:A->complex).
        sigma zero = Cx(&0) /\
        sigma one_value = Cx(&1) /\
        (!x y:A. sigma (add x y) = sigma x + sigma y) /\
        (!x y:A. sigma (mul x y) = sigma x * sigma y) /\
        (!x y:A. sigma x = sigma y ==> x = y) in
   let place_equivalent =
      \(sigma:A->complex) (tau:A->complex).
        (!x:A. tau x = sigma x) \/
        (!x:A. tau x = cnj (sigma x)) in
   let infinite_places =
      \(zero:A) (one_value:A) (add:A->A->A) (mul:A->A->A)
       (places:(A->complex)->bool).
        FINITE places /\
        (!p. p IN places ==> field_embedding zero one_value add mul p) /\
        (!sigma.
           field_embedding zero one_value add mul sigma
           ==> ?!p. p IN places /\ place_equivalent sigma p) in
   let valid_coefficients =
      \(rank:num) (coefficients:num->int).
        !i. rank <= i ==> coefficients i = &0 in
   let unit_product =
      \(mul:A->A->A) (inv:A->A) (rank:num)
       (fundamental_unit:num->A) (coefficients:num->int).
        finite_product mul rank
          (\i. integer_power mul inv
                 (fundamental_unit i) (coefficients i)) in
   let basis_mod_torsion =
      \(zero:A) (one_value:A) (add:A->A->A) (mul:A->A->A)
       (inv:A->A) (of_int:int->A) (rank:num)
       (fundamental_unit:num->A).
        (!i. i < rank
             ==> unit zero one_value add mul inv of_int
                   (fundamental_unit i)) /\
        (!coefficients.
           valid_coefficients rank coefficients /\
           torsion_unit zero one_value add mul inv of_int
             (unit_product mul inv rank
               fundamental_unit coefficients)
           ==> !i. i < rank ==> coefficients i = &0) /\
        (!x.
           unit zero one_value add mul inv of_int x
           ==> ?zeta coefficients.
                 torsion_unit zero one_value add mul inv of_int zeta /\
                 valid_coefficients rank coefficients /\
                 x =
                 mul zeta
                   (unit_product mul inv rank
                     fundamental_unit coefficients)) in
   !zero:A one_value:A add:A->A->A mul:A->A->A
    neg:A->A inv:A->A of_int:int->A
    places:(A->complex)->bool.
     number_field zero one_value add mul neg inv of_int /\
     infinite_places zero one_value add mul places
     ==>
     ?fundamental_unit:num->A.
       let rank = CARD places - 1 in
       basis_mod_torsion zero one_value add mul inv of_int
         rank fundamental_unit /\
       !x.
         unit zero one_value add mul inv of_int x
         ==> ?!decomposition:A#(num->int).
               torsion_unit zero one_value add mul inv of_int
                 (FST decomposition) /\
               valid_coefficients rank (SND decomposition) /\
               x =
               mul (FST decomposition)
                 (unit_product mul inv rank
                   fundamental_unit (SND decomposition))`;;
