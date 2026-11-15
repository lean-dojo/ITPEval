(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1551745
  (thousand-theorems__hol-light__Q1551745), "Binomial inverse theorem": the
  inverse of A + U C V over an arbitrary noncommutative ring is expressed in
  terms of the inverses of A and C + C V A^-1 U C. This file contains no proof.
*)

let q1551745_noncommutative_ring = new_definition
 `q1551745_noncommutative_ring
    (zero:A) (unity:A) (neg:A->A) (add:A->A->A) (mul:A->A->A) <=>
    (!x y z:A. add (add x y) z = add x (add y z)) /\
    (!x y:A. add x y = add y x) /\
    (!x:A. add zero x = x) /\
    (!x:A. add (neg x) x = zero) /\
    (!x y z:A. mul (mul x y) z = mul x (mul y z)) /\
    (!x:A. mul unity x = x) /\
    (!x:A. mul x unity = x) /\
    (!x y z:A. mul x (add y z) = add (mul x y) (mul x z)) /\
    (!x y z:A. mul (add x y) z = add (mul x z) (mul y z))`;;

let q1551745_matrix_eq = new_definition
 `q1551745_matrix_eq (rows:I->bool) (cols:J->bool)
                     (x:I->J->A) (y:I->J->A) <=>
    !i j. i IN rows /\ j IN cols ==> x i j = y i j`;;

let q1551745_matrix_add = new_definition
 `q1551745_matrix_add (add:A->A->A)
                      (x:I->J->A) (y:I->J->A) =
    \i j. add (x i j) (y i j)`;;

let q1551745_matrix_sub = new_definition
 `q1551745_matrix_sub (add:A->A->A) (neg:A->A)
                      (x:I->J->A) (y:I->J->A) =
    \i j. add (x i j) (neg (y i j))`;;

let q1551745_matrix_mul = new_definition
 `q1551745_matrix_mul (middle:K->bool)
                      (add:A->A->A) (mul:A->A->A)
                      (x:I->K->A) (y:K->J->A) =
    \i j. iterate add middle (\k. mul (x i k) (y k j))`;;

let q1551745_matrix_one = new_definition
 `q1551745_matrix_one (zero:A) (unity:A) (i:I) (j:I) =
    if i = j then unity else zero`;;

let q1551745_matrix_invertible = new_definition
 `q1551745_matrix_invertible
    (indices:I->bool) (zero:A) (unity:A)
    (add:A->A->A) (mul:A->A->A) (x:I->I->A) <=>
    ?y:I->I->A.
      q1551745_matrix_eq indices indices
        (q1551745_matrix_mul indices add mul x y)
        (q1551745_matrix_one zero unity) /\
      q1551745_matrix_eq indices indices
        (q1551745_matrix_mul indices add mul y x)
        (q1551745_matrix_one zero unity)`;;

let q1551745_matrix_inv = new_definition
 `q1551745_matrix_inv
    (indices:I->bool) (zero:A) (unity:A)
    (add:A->A->A) (mul:A->A->A) (x:I->I->A) =
    @y:I->I->A.
      q1551745_matrix_eq indices indices
        (q1551745_matrix_mul indices add mul x y)
        (q1551745_matrix_one zero unity) /\
      q1551745_matrix_eq indices indices
        (q1551745_matrix_mul indices add mul y x)
        (q1551745_matrix_one zero unity)`;;

let Q1551745_BINOMIAL_INVERSE_THEOREM =
 `!zero:A. !unity:A. !neg:A->A. !add:A->A->A. !mul:A->A->A.
  !nindex:N->bool. !mindex:M->bool.
    q1551745_noncommutative_ring zero unity neg add mul /\
    FINITE nindex /\ FINITE mindex
    ==>
    !a:N->N->A. !u:N->M->A. !c:M->M->A. !v:M->N->A.
      let ainv =
        q1551745_matrix_inv nindex zero unity add mul a in
      let d =
        q1551745_matrix_add add c
          (q1551745_matrix_mul mindex add mul
            (q1551745_matrix_mul nindex add mul
              (q1551745_matrix_mul nindex add mul
                (q1551745_matrix_mul mindex add mul c v) ainv) u) c) in
      let dinv =
        q1551745_matrix_inv mindex zero unity add mul d in
      let s =
        q1551745_matrix_add add a
          (q1551745_matrix_mul mindex add mul
            (q1551745_matrix_mul mindex add mul u c) v) in
      let correction =
        q1551745_matrix_mul nindex add mul
          (q1551745_matrix_mul mindex add mul
            (q1551745_matrix_mul mindex add mul
              (q1551745_matrix_mul mindex add mul
                (q1551745_matrix_mul mindex add mul
                  (q1551745_matrix_mul nindex add mul ainv u) c) dinv) c) v)
          ainv in
      q1551745_matrix_invertible nindex zero unity add mul a /\
      q1551745_matrix_invertible mindex zero unity add mul d /\
      q1551745_matrix_invertible nindex zero unity add mul s
      ==>
      q1551745_matrix_eq nindex nindex
        (q1551745_matrix_inv nindex zero unity add mul s)
        (q1551745_matrix_sub add neg ainv correction)`;;
