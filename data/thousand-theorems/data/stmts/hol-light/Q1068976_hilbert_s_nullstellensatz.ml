(*
  Statement-only formalization of Thousand Theorems artifact Q1068976,
  "Hilbert's Nullstellensatz": over a field embedded in an algebraically
  closed field, the ideal of multivariate polynomials vanishing on the common
  zero locus of an ideal is its radical. This file contains no proof.
*)

let HILBERTS_NULLSTELLENSATZ =
  `let is_field_A =
     \(z:A) (unitA:A) (add:A->A->A) (mul:A->A->A)
      (negA0:A->A) (invA0:A->A).
       ~(z = unitA) /\
       (!x. add z x = x) /\
       (!x. add (negA0 x) x = z) /\
       (!x y. add x y = add y x) /\
       (!x y w. add x (add y w) = add (add x y) w) /\
       (!x. mul unitA x = x) /\
       (!x y. mul x y = mul y x) /\
       (!x y w. mul x (mul y w) = mul (mul x y) w) /\
       (!x y w. mul x (add y w) = add (mul x y) (mul x w)) /\
       (!x. ~(x = z) ==> mul (invA0 x) x = unitA) in
   let is_field_B =
     \(z:B) (unitB:B) (add:B->B->B) (mul:B->B->B)
      (negB0:B->B) (invB0:B->B).
       ~(z = unitB) /\
       (!x. add z x = x) /\
       (!x. add (negB0 x) x = z) /\
       (!x y. add x y = add y x) /\
       (!x y w. add x (add y w) = add (add x y) w) /\
       (!x. mul unitB x = x) /\
       (!x y. mul x y = mul y x) /\
       (!x y w. mul x (mul y w) = mul (mul x y) w) /\
       (!x y w. mul x (add y w) = add (mul x y) (mul x w)) /\
       (!x. ~(x = z) ==> mul (invB0 x) x = unitB) in
   let power_B =
     \(unitB:B) (mul:B->B->B) (x:B) (n:num).
       ITLIST mul (REPLICATE n x) unitB in
   let is_polynomial =
     \(z:A) (vars:V->bool) (p:(V->num)->A).
       FINITE {m | ~(p m = z)} /\
       (!m i. ~(p m = z) /\ ~(i IN vars) ==> m i = 0) in
   let polynomial_zero =
     \(z:A). \(m:V->num). z in
   let polynomial_one =
     \(z:A) (unitA:A). \(m:V->num).
       if (!i. m i = 0) then unitA else z in
   let polynomial_neg =
     \(negA0:A->A) (p:(V->num)->A). \m. negA0 (p m) in
   let polynomial_add =
     \(add:A->A->A) (p:(V->num)->A) (q:(V->num)->A).
       \m. add (p m) (q m) in
   let polynomial_mul =
     \(z:A) (add:A->A->A) (mul:A->A->A)
      (p:(V->num)->A) (q:(V->num)->A).
       \m. iterate add
             {(u,v) |
                ~(p u = z) /\
                ~(q v = z) /\
                (!i. m i = u i + v i)}
             (\(u,v). mul (p u) (q v)) in
   let polynomial_power =
     \(z:A) (unitA:A) (add:A->A->A) (mul:A->A->A)
      (p:(V->num)->A) (n:num).
       ITLIST (polynomial_mul z add mul)
              (REPLICATE n p)
              (polynomial_one z unitA) in
   let polynomial_eval =
     \(zA:A) (h:A->B) (zB:B) (oB:B)
      (addB:B->B->B) (mulB:B->B->B)
      (vars:V->bool) (p:(V->num)->A) (x:V->B).
       iterate addB {m | ~(p m = zA)}
         (\m. mulB (h (p m))
               (iterate mulB vars
                 (\i. power_B oB mulB (x i) (m i)))) in
   let is_univariate_polynomial =
     \(z:B) (p:num->B). FINITE {n | ~(p n = z)} in
   let univariate_eval =
     \(z:B) (unitB:B) (add:B->B->B) (mul:B->B->B)
      (p:num->B) (x:B).
       iterate add {n | ~(p n = z)}
         (\n. mul (p n) (power_B unitB mul x n)) in
   let is_algebraically_closed =
     \(z:B) (unitB:B) (add:B->B->B) (mul:B->B->B).
       !p:num->B.
         is_univariate_polynomial z p /\
         (?n. ~(n = 0) /\ ~(p n = z))
         ==> ?x:B. univariate_eval z unitB add mul p x = z in
   let is_ideal =
     \(z:A) (unitA:A) (add:A->A->A) (mul:A->A->A)
      (negA0:A->A) (vars:V->bool) (ideal:((V->num)->A)->bool).
       (!p. ideal p ==> is_polynomial z vars p) /\
       ideal (polynomial_zero z) /\
       (!p. ideal p ==> ideal (polynomial_neg negA0 p)) /\
       (!p q. ideal p /\ ideal q ==> ideal (polynomial_add add p q)) /\
       (!a p.
          is_polynomial z vars a /\ ideal p
          ==> ideal (polynomial_mul z add mul a p)) in
   let zero_locus =
     \(zA:A) (h:A->B) (zB:B) (oB:B)
      (addB:B->B->B) (mulB:B->B->B)
      (vars:V->bool) (ideal:((V->num)->A)->bool).
       {x:V->B |
          !p. ideal p
              ==> polynomial_eval zA h zB oB addB mulB vars p x = zB} in
   let vanishing_ideal =
     \(zA:A) (h:A->B) (zB:B) (oB:B)
      (addB:B->B->B) (mulB:B->B->B)
      (vars:V->bool) (ideal:((V->num)->A)->bool).
       {p:(V->num)->A |
          is_polynomial zA vars p /\
          !x. x IN zero_locus zA h zB oB addB mulB vars ideal
              ==> polynomial_eval zA h zB oB addB mulB vars p x = zB} in
   let radical_ideal =
     \(z:A) (unitA:A) (add:A->A->A) (mul:A->A->A)
      (vars:V->bool) (ideal:((V->num)->A)->bool).
       {p:(V->num)->A |
          is_polynomial z vars p /\
          ?n. ~(n = 0) /\
              ideal (polynomial_power z unitA add mul p n)} in
   !zA:A. !oA:A. !addA:A->A->A. !mulA:A->A->A.
   !negA:A->A. !invA:A->A.
   !zB:B. !oB:B. !addB:B->B->B. !mulB:B->B->B.
   !negB:B->B. !invB:B->B. !h:A->B.
   !vars:V->bool. !ideal:((V->num)->A)->bool.
     is_field_A zA oA addA mulA negA invA /\
     is_field_B zB oB addB mulB negB invB /\
     h zA = zB /\
     h oA = oB /\
     (!x y. h (addA x y) = addB (h x) (h y)) /\
     (!x y. h (mulA x y) = mulB (h x) (h y)) /\
     is_algebraically_closed zB oB addB mulB /\
     FINITE vars /\
     is_ideal zA oA addA mulA negA vars ideal
     ==> vanishing_ideal zA h zB oB addB mulB vars ideal =
         radical_ideal zA oA addA mulA vars ideal`;;
