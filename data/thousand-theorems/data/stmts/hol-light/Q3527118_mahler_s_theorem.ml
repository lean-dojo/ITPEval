(*
  Statement-only formalization of Thousand Theorems corpus artifact Q3527118,
  "Mahler's theorem": the Mahler series of a continuous function on the
  p-adic integers, with coefficients given by iterated forward differences,
  converges uniformly to that function. This file contains no proof.
*)

needs "Library/binomial.ml";;

let Q3527118_MAHLER_S_THEOREM =
 `let padic_nat_distance =
      \p:num. \m n:num.
        if m = n then &0
        else
          let d = if m <= n then n - m else m - n in
          inv
            ((&p) pow
             (@k:num.
                (p EXP k) divides d /\
                ~((p EXP (SUC k)) divides d))) in
   let complete_metric =
      \(metric:P->P->real).
        !u:num->P.
          (!epsilon:real.
             &0 < epsilon
             ==> ?N:num.
                   !m n:num.
                     N <= m /\ N <= n
                     ==> metric (u m) (u n) < epsilon)
          ==> ?limit:P.
                !epsilon:real.
                  &0 < epsilon
                  ==> ?N:num.
                        !n:num.
                          N <= n
                          ==> metric (u n) limit < epsilon in
   let padic_integer_model =
      \p:num.
       \(pzero:P) (pone:P) (padd:P->P->P) (pneg:P->P)
       (pmul:P->P->P) (of_num:num->P) (pdist:P->P->real).
        (!x y:P. padd x y = padd y x) /\
        (!x y z:P. padd (padd x y) z = padd x (padd y z)) /\
        (!x:P. padd x pzero = x) /\
        (!x:P. padd x (pneg x) = pzero) /\
        (!x y:P. pmul x y = pmul y x) /\
        (!x y z:P. pmul (pmul x y) z = pmul x (pmul y z)) /\
        (!x:P. pmul x pone = x) /\
        (!x y z:P.
           pmul x (padd y z) =
           padd (pmul x y) (pmul x z)) /\
        of_num 0 = pzero /\
        of_num 1 = pone /\
        (!m n:num. of_num (m + n) = padd (of_num m) (of_num n)) /\
        (!m n:num. of_num (m * n) = pmul (of_num m) (of_num n)) /\
        (!x y:P. &0 <= pdist x y) /\
        (!x y:P. pdist x y = &0 <=> x = y) /\
        (!x y:P. pdist x y = pdist y x) /\
        (!x y z:P.
           pdist x z <= max (pdist x y) (pdist y z)) /\
        (!x y z:P.
           pdist (padd x z) (padd y z) = pdist x y) /\
        (!x y:P.
           pdist pzero (pmul x y) =
           pdist pzero x * pdist pzero y) /\
        complete_metric pdist /\
        (!x:P. !epsilon:real.
           &0 < epsilon
           ==> ?n:num. pdist (of_num n) x < epsilon) /\
        (!m n:num.
           pdist (of_num m) (of_num n) =
           padic_nat_distance p m n) in
   let mahler_basis =
      \(of_num:num->P) (pdist:P->P->real) (mahler:num->P->P).
        (!k n:num.
           mahler k (of_num n) = of_num (binom (n,k))) /\
        (!k:num. !x:P. !epsilon:real.
           &0 < epsilon
           ==> ?delta:real.
                 &0 < delta /\
                 !y:P.
                   pdist y x < delta
                   ==> pdist (mahler k y) (mahler k x) < epsilon) in
   let normed_add_comm_group =
      \(zero:A) (add:A->A->A) (neg:A->A) (norm:A->real).
        (!x y:A. add x y = add y x) /\
        (!x y z:A. add (add x y) z = add x (add y z)) /\
        (!x:A. add x zero = x) /\
        (!x:A. add x (neg x) = zero) /\
        (!x:A. &0 <= norm x) /\
        (!x:A. norm x = &0 <=> x = zero) /\
        (!x:A. norm (neg x) = norm x) in
   let ultrametric_norm =
      \(add:A->A->A) (norm:A->real).
        !x y:A. norm (add x y) <= max (norm x) (norm y) in
   let complete_normed_group =
      \(add:A->A->A) (neg:A->A) (norm:A->real).
        !u:num->A.
          (!epsilon:real.
             &0 < epsilon
             ==> ?N:num.
                   !m n:num.
                     N <= m /\ N <= n
                     ==> norm (add (u m) (neg (u n))) < epsilon)
          ==> ?limit:A.
                !epsilon:real.
                  &0 < epsilon
                  ==> ?N:num.
                        !n:num.
                          N <= n
                          ==> norm
                                (add (u n) (neg limit)) < epsilon in
   let module_over_padic_integers =
      \(pzero:P) (pone:P) (padd:P->P->P) (pmul:P->P->P)
       (zero:A) (add:A->A->A) (smul:P->A->A).
        (!x:A. smul pone x = x) /\
        (!r s:P. !x:A.
           smul (pmul r s) x = smul r (smul s x)) /\
        (!r s:P. !x:A.
           smul (padd r s) x = add (smul r x) (smul s x)) /\
        (!r:P. !x y:A.
           smul r (add x y) = add (smul r x) (smul r y)) /\
        (!x:A. smul pzero x = zero) /\
        (!r:P. smul r zero = zero) in
   let bounded_padic_smul =
      \(pzero:P) (pdist:P->P->real)
       (smul:P->A->A) (norm:A->real).
        !r:P. !x:A.
          norm (smul r x) <= pdist pzero r * norm x in
   let continuous_function =
      \(pdist:P->P->real)
       (add:A->A->A) (neg:A->A) (norm:A->real) (f:P->A).
        !x:P. !epsilon:real.
          &0 < epsilon
          ==> ?delta:real.
                &0 < delta /\
                !y:P.
                  pdist y x < delta
                  ==> norm (add (f y) (neg (f x))) < epsilon in
   let forward_difference =
      \(pone:P) (padd:P->P->P)
       (add:A->A->A) (neg:A->A) (f:P->A) (n:num).
        (@differences:num->P->A.
           differences 0 = f /\
           (!k:num. !x:P.
              differences (SUC k) x =
              add (differences k (padd x pone))
                  (neg (differences k x)))) n in
   let mahler_term =
      \(pzero:P) (pone:P) (padd:P->P->P)
       (add:A->A->A) (neg:A->A) (smul:P->A->A)
       (mahler:num->P->P) (f:P->A) (n:num) (x:P).
        smul (mahler n x)
          ((forward_difference pone padd add neg f n) pzero) in
   let partial_sum =
      \(pzero:P) (pone:P) (padd:P->P->P)
       (zero:A) (add:A->A->A) (neg:A->A)
       (smul:P->A->A) (mahler:num->P->P)
       (f:P->A) (n:num) (x:P).
        (@sums:num->P->A.
           (!y:P. sums 0 y = zero) /\
           (!k:num. !y:P.
              sums (SUC k) y =
              add (sums k y)
                (mahler_term
                  pzero pone padd add neg smul mahler f k y))) n x in
   !p:num.
   !pzero:P.
   !pone:P.
   !padd:P->P->P.
   !pneg:P->P.
   !pmul:P->P->P.
   !of_num:num->P.
   !pdist:P->P->real.
   !mahler:num->P->P.
   !zero:A.
   !add:A->A->A.
   !neg:A->A.
   !smul:P->A->A.
   !norm:A->real.
   !f:P->A.
     prime p /\
     padic_integer_model
       p pzero pone padd pneg pmul of_num pdist /\
     mahler_basis of_num pdist mahler /\
     normed_add_comm_group zero add neg norm /\
     ultrametric_norm add norm /\
     complete_normed_group add neg norm /\
     module_over_padic_integers
       pzero pone padd pmul zero add smul /\
     bounded_padic_smul pzero pdist smul norm /\
     continuous_function pdist add neg norm f
     ==> !epsilon:real.
           &0 < epsilon
           ==> ?N:num.
                 !n:num.
                   N <= n
                   ==> !x:P.
                         norm
                           (add
                             (partial_sum
                               pzero pone padd zero add neg smul
                               mahler f n x)
                             (neg (f x))) < epsilon`;;
