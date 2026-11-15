(*
  Statement-only formalization of Thousand Theorems corpus artifact Q939927
  (thousand-theorems__hol-light__Q939927), "Stone–Weierstrass theorem": on an
  arbitrary compact topological space, every real subalgebra of continuous
  functions that separates points is uniformly dense in all real-valued
  continuous functions. This file contains no proof.
*)

let Q939927_STONE_WEIERSTRASS_THEOREM =
  `let is_topology =
     \(carrier:A->bool) (opens:(A->bool)->bool).
       opens {} /\
       opens carrier /\
       (!u:A->bool. opens u ==> u SUBSET carrier) /\
       (!family:(A->bool)->bool.
          (!u:A->bool. u IN family ==> opens u)
          ==> opens (UNIONS family)) /\
       (!u v:A->bool.
          opens u /\ opens v ==> opens (u INTER v)) in
   let real_open =
     \u:real->bool.
       !x:real.
         x IN u
         ==> ?epsilon:real.
               &0 < epsilon /\
               !y:real. abs(y - x) < epsilon ==> y IN u in
   let continuous_real =
     \(carrier:A->bool) (opens:(A->bool)->bool) (f:A->real).
       !u:real->bool.
         real_open u
         ==> opens {x:A | x IN carrier /\ f x IN u} in
   let compact_space =
     \(carrier:A->bool) (opens:(A->bool)->bool).
       !cover:(A->bool)->bool.
         (!u:A->bool. u IN cover ==> opens u) /\
         carrier SUBSET UNIONS cover
         ==> ?finite_cover:(A->bool)->bool.
               finite_cover SUBSET cover /\
               FINITE finite_cover /\
               carrier SUBSET UNIONS finite_cover in
   let agrees_on =
     \(carrier:A->bool) (f:A->real) (g:A->real).
       !x:A. x IN carrier ==> f x = g x in
   !carrier:A->bool.
   !opens:(A->bool)->bool.
   !alg:(A->real)->bool.
     is_topology carrier opens /\
     compact_space carrier opens /\
     (!f g:A->real.
        agrees_on carrier f g ==> (alg f <=> alg g)) /\
     (!f:A->real. alg f ==> continuous_real carrier opens f) /\
     (!c:real. alg (\x:A. c)) /\
     (!f g:A->real.
        alg f /\ alg g ==> alg (\x:A. f x + g x)) /\
     (!f g:A->real.
        alg f /\ alg g ==> alg (\x:A. f x * g x)) /\
     (!x y:A.
        x IN carrier /\ y IN carrier /\ ~(x = y)
        ==> ?f:A->real. alg f /\ ~(f x = f y))
     ==> !f:A->real.
           continuous_real carrier opens f
           ==> !epsilon:real.
                 &0 < epsilon
                 ==> ?g:A->real.
                       alg g /\
                       !x:A.
                         x IN carrier
                         ==> abs(f x - g x) < epsilon`;;
