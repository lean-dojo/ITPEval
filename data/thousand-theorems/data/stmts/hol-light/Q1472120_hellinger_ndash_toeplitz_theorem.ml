(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1472120,
  "Hellinger--Toeplitz theorem": every symmetric linear operator defined on an
  arbitrary complete real or complex inner-product space is continuous. This
  file contains no proof.
*)

let q1472120_output = open_out "/dev/null";;
let q1472120_formatter = Format.formatter_of_out_channel q1472120_output;;
let q1472120_previous_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file q1472120_formatter path);;
let q1472120_loaded =
  Toploop.use_file q1472120_formatter "Complex/complexnumbers.ml";;
Hol_loader.file_loader := q1472120_previous_loader;;
Format.pp_print_flush q1472120_formatter ();;
close_out q1472120_output;;
if not q1472120_loaded then failwith "Unable to load complex library";;

let Q1472120_HELLINGER_TOEPLITZ_THEOREM =
 `let real_vector_space =
    \(zero:V) (add:V->V->V) (neg:V->V) (smul:real->V->V).
      (!x y z:V. add x (add y z) = add (add x y) z) /\
      (!x y:V. add x y = add y x) /\
      (!x:V. add zero x = x) /\
      (!x:V. add (neg x) x = zero) /\
      (!x:V. smul (&1) x = x) /\
      (!a b:real. !x:V.
         smul (a * b) x = smul a (smul b x)) /\
      (!a b:real. !x:V.
         smul (a + b) x = add (smul a x) (smul b x)) /\
      (!a:real. !x y:V.
         smul a (add x y) = add (smul a x) (smul a y)) in
  let real_inner_product =
    \(zero:V) (add:V->V->V) (smul:real->V->V)
     (inner:V->V->real).
      (!x y z:V.
         inner (add x y) z = inner x z + inner y z) /\
      (!a:real. !x y:V.
         inner (smul a x) y = a * inner x y) /\
      (!x y:V. inner x y = inner y x) /\
      (!x:V. &0 <= inner x x) /\
      (!x:V. inner x x = &0 <=> x = zero) in
  let real_vector_norm =
    \(inner:V->V->real) (x:V). sqrt(inner x x) in
  let real_tends_to =
    \(add:V->V->V) (neg:V->V) (inner:V->V->real)
     (u:num->V) (x:V).
      !epsilon:real.
        &0 < epsilon
        ==> ?N:num. !n:num.
              N <= n
              ==> real_vector_norm inner
                    (add (u n) (neg x)) < epsilon in
  let real_complete =
    \(add:V->V->V) (neg:V->V) (inner:V->V->real).
      !u:num->V.
        (!epsilon:real.
           &0 < epsilon
           ==> ?N:num. !m n:num.
                 N <= m /\ N <= n
                 ==> real_vector_norm inner
                       (add (u m) (neg (u n))) < epsilon)
        ==> ?x:V. real_tends_to add neg inner u x in
  let real_linear =
    \(add:V->V->V) (smul:real->V->V) (op:V->V).
      (!x y:V. op (add x y) = add (op x) (op y)) /\
      (!a:real. !x:V. op (smul a x) = smul a (op x)) in
  let real_symmetric =
    \(inner:V->V->real) (op:V->V).
      !x y:V. inner (op x) y = inner x (op y) in
  let real_continuous =
    \(add:V->V->V) (neg:V->V) (inner:V->V->real)
     (op:V->V).
      !x:V. !epsilon:real.
        &0 < epsilon
        ==> ?delta:real.
              &0 < delta /\
              !y:V.
                real_vector_norm inner (add y (neg x)) < delta
                ==> real_vector_norm inner
                      (add (op y) (neg (op x))) < epsilon in
  let complex_vector_space =
    \(zero:W) (add:W->W->W) (neg:W->W)
     (smul:complex->W->W).
      (!x y z:W. add x (add y z) = add (add x y) z) /\
      (!x y:W. add x y = add y x) /\
      (!x:W. add zero x = x) /\
      (!x:W. add (neg x) x = zero) /\
      (!x:W. smul (Cx(&1)) x = x) /\
      (!a b:complex. !x:W.
         smul (a * b) x = smul a (smul b x)) /\
      (!a b:complex. !x:W.
         smul (a + b) x = add (smul a x) (smul b x)) /\
      (!a:complex. !x y:W.
         smul a (add x y) = add (smul a x) (smul a y)) in
  let complex_inner_product =
    \(zero:W) (add:W->W->W) (smul:complex->W->W)
     (inner:W->W->complex).
      (!x y z:W.
         inner (add x y) z = inner x z + inner y z) /\
      (!a:complex. !x y:W.
         inner (smul a x) y = cnj(a) * inner x y) /\
      (!x y:W. cnj(inner y x) = inner x y) /\
      (!x:W. Im(inner x x) = &0 /\ &0 <= Re(inner x x)) /\
      (!x:W. inner x x = Cx(&0) <=> x = zero) in
  let complex_vector_norm =
    \(inner:W->W->complex) (x:W). sqrt(Re(inner x x)) in
  let complex_tends_to =
    \(add:W->W->W) (neg:W->W) (inner:W->W->complex)
     (u:num->W) (x:W).
      !epsilon:real.
        &0 < epsilon
        ==> ?N:num. !n:num.
              N <= n
              ==> complex_vector_norm inner
                    (add (u n) (neg x)) < epsilon in
  let complex_complete =
    \(add:W->W->W) (neg:W->W) (inner:W->W->complex).
      !u:num->W.
        (!epsilon:real.
           &0 < epsilon
           ==> ?N:num. !m n:num.
                 N <= m /\ N <= n
                 ==> complex_vector_norm inner
                       (add (u m) (neg (u n))) < epsilon)
        ==> ?x:W. complex_tends_to add neg inner u x in
  let complex_linear =
    \(add:W->W->W) (smul:complex->W->W) (op:W->W).
      (!x y:W. op (add x y) = add (op x) (op y)) /\
      (!a:complex. !x:W. op (smul a x) = smul a (op x)) in
  let complex_symmetric =
    \(inner:W->W->complex) (op:W->W).
      !x y:W. inner (op x) y = inner x (op y) in
  let complex_continuous =
    \(add:W->W->W) (neg:W->W) (inner:W->W->complex)
     (op:W->W).
      !x:W. !epsilon:real.
        &0 < epsilon
        ==> ?delta:real.
              &0 < delta /\
              !y:W.
                complex_vector_norm inner (add y (neg x)) < delta
                ==> complex_vector_norm inner
                      (add (op y) (neg (op x))) < epsilon in
  ((!zero:V.
    !add:V->V->V.
    !neg:V->V.
    !smul:real->V->V.
    !inner:V->V->real.
      real_vector_space zero add neg smul /\
      real_inner_product zero add smul inner /\
      real_complete add neg inner
      ==> !op:V->V.
            real_linear add smul op /\
            real_symmetric inner op
            ==> real_continuous add neg inner op) /\
   (!zero:W.
    !add:W->W->W.
    !neg:W->W.
    !smul:complex->W->W.
    !inner:W->W->complex.
      complex_vector_space zero add neg smul /\
      complex_inner_product zero add smul inner /\
      complex_complete add neg inner
      ==> !op:W->W.
            complex_linear add smul op /\
            complex_symmetric inner op
            ==> complex_continuous add neg inner op))`;;
