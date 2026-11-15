(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1357684,
  "Riesz representation theorem": inner product with a vector gives a
  conjugate-linear isometric equivalence from an arbitrary real or complex
  Hilbert space to its continuous dual. This file contains no proof.
*)

let q1357684_output = open_out "/dev/null";;
let q1357684_formatter = Format.formatter_of_out_channel q1357684_output;;
let q1357684_previous_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file q1357684_formatter path);;
let q1357684_loaded =
  Toploop.use_file q1357684_formatter "Complex/complexnumbers.ml";;
Hol_loader.file_loader := q1357684_previous_loader;;
Format.pp_print_flush q1357684_formatter ();;
close_out q1357684_output;;
if not q1357684_loaded then failwith "Unable to load complex library";;

let Q1357684_RIESZ_REPRESENTATION_THEOREM =
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
              ==> real_vector_norm inner (add (u n) (neg x)) < epsilon in
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
  let real_continuous_linear =
    \(add:V->V->V) (smul:real->V->V) (inner:V->V->real)
     (l:V->real).
      (!x y:V. l (add x y) = l x + l y) /\
      (!a:real. !x:V. l (smul a x) = a * l x) /\
      (?C:real.
         &0 <= C /\
         !x:V. abs(l x) <= C * real_vector_norm inner x) in
  let real_has_dual_norm =
    \(inner:V->V->real) (l:V->real) (r:real).
      &0 <= r /\
      (!x:V. abs(l x) <= r * real_vector_norm inner x) /\
      (!C:real.
         &0 <= C /\
         (!x:V. abs(l x) <= C * real_vector_norm inner x)
         ==> r <= C) in
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
  let complex_continuous_linear =
    \(add:W->W->W) (smul:complex->W->W)
     (inner:W->W->complex) (l:W->complex).
      (!x y:W. l (add x y) = l x + l y) /\
      (!a:complex. !x:W. l (smul a x) = a * l x) /\
      (?C:real.
         &0 <= C /\
         !x:W. norm(l x) <= C * complex_vector_norm inner x) in
  let complex_has_dual_norm =
    \(inner:W->W->complex) (l:W->complex) (r:real).
      &0 <= r /\
      (!x:W. norm(l x) <= r * complex_vector_norm inner x) /\
      (!C:real.
         &0 <= C /\
         (!x:W. norm(l x) <= C * complex_vector_norm inner x)
         ==> r <= C) in
  ((!zero:V.
    !add:V->V->V.
    !neg:V->V.
    !smul:real->V->V.
    !inner:V->V->real.
      real_vector_space zero add neg smul /\
      real_inner_product zero add smul inner /\
      real_complete add neg inner
      ==> ?to_dual:V->V->real.
          ?from_dual:(V->real)->V.
            (!x y:V. to_dual x y = inner x y) /\
            (!x:V.
               real_continuous_linear add smul inner (to_dual x)) /\
            (!x:V.
               real_has_dual_norm inner (to_dual x)
                 (real_vector_norm inner x)) /\
            (!x:V. from_dual (to_dual x) = x) /\
            (!l:V->real.
               real_continuous_linear add smul inner l
               ==> to_dual (from_dual l) = l)) /\
   (!zero:W.
    !add:W->W->W.
    !neg:W->W.
    !smul:complex->W->W.
    !inner:W->W->complex.
      complex_vector_space zero add neg smul /\
      complex_inner_product zero add smul inner /\
      complex_complete add neg inner
      ==> ?to_dual:W->W->complex.
          ?from_dual:(W->complex)->W.
            (!x y:W. to_dual x y = inner x y) /\
            (!x:W.
               complex_continuous_linear add smul inner (to_dual x)) /\
            (!x:W.
               complex_has_dual_norm inner (to_dual x)
                 (complex_vector_norm inner x)) /\
            (!x:W. from_dual (to_dual x) = x) /\
            (!l:W->complex.
               complex_continuous_linear add smul inner l
               ==> to_dual (from_dual l) = l)))`;;
