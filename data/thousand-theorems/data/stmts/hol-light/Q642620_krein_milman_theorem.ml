(*
  Statement-only formalization of Thousand Theorems corpus artifact Q642620,
  "Krein-Milman theorem": every compact convex subset of a Hausdorff locally
  convex real topological vector space is the closure of the convex hull of
  its extreme points. This file contains no proof.
*)

let Q642620_KREIN_MILMAN_THEOREM =
  `let is_topology =
     \(open_sets:(A->bool)->bool).
       open_sets {} /\
       open_sets (UNIV:A->bool) /\
       (!C:(A->bool)->bool.
          (!U:A->bool. U IN C ==> open_sets U)
          ==> open_sets (UNIONS C)) /\
       (!U V:A->bool.
          open_sets U /\ open_sets V
          ==> open_sets (U INTER V)) in
   let is_hausdorff =
     \(open_sets:(A->bool)->bool).
       !x y:A.
         ~(x = y)
         ==> ?U V:A->bool.
               open_sets U /\
               open_sets V /\
               x IN U /\
               y IN V /\
               U INTER V = {} in
   let real_vector_space =
     \(zero:A) (add:A->A->A) (neg:A->A)
      (smul:real->A->A).
       (!x y z:A. add x (add y z) = add (add x y) z) /\
       (!x y:A. add x y = add y x) /\
       (!x:A. add zero x = x) /\
       (!x:A. add (neg x) x = zero) /\
       (!x:A. smul (&1) x = x) /\
       (!a b:real. !x:A.
          smul (a * b) x = smul a (smul b x)) /\
       (!a b:real. !x:A.
          smul (a + b) x = add (smul a x) (smul b x)) /\
       (!a:real. !x y:A.
          smul a (add x y) = add (smul a x) (smul a y)) /\
       (!x:A. smul (&0) x = zero) /\
       (!a:real. smul a zero = zero) in
   let convex_set =
     \(add:A->A->A) (smul:real->A->A) (s:A->bool).
       !x y:A. !a b:real.
         x IN s /\
         y IN s /\
         &0 <= a /\
         &0 <= b /\
         a + b = &1
         ==> add (smul a x) (smul b y) IN s in
   let is_topological_add_group =
     \(add:A->A->A) (neg:A->A)
      (open_sets:(A->bool)->bool).
       (!x y:A. !U:A->bool.
          open_sets U /\ add x y IN U
          ==> ?V W:A->bool.
                open_sets V /\
                open_sets W /\
                x IN V /\
                y IN W /\
                (!v w:A.
                   v IN V /\ w IN W ==> add v w IN U)) /\
       (!x:A. !U:A->bool.
          open_sets U /\ neg x IN U
          ==> ?V:A->bool.
                open_sets V /\
                x IN V /\
                (!v:A. v IN V ==> neg v IN U)) in
   let has_continuous_smul =
     \(smul:real->A->A) (open_sets:(A->bool)->bool).
       !a:real. !x:A. !U:A->bool.
         open_sets U /\ smul a x IN U
         ==> ?epsilon:real. ?V:A->bool.
               &0 < epsilon /\
               open_sets V /\
               x IN V /\
               (!b:real. !y:A.
                  abs(b - a) < epsilon /\ y IN V
                  ==> smul b y IN U) in
   let is_locally_convex =
     \(add:A->A->A) (smul:real->A->A)
      (open_sets:(A->bool)->bool).
       !x:A. !U:A->bool.
         open_sets U /\ x IN U
         ==> ?V W:A->bool.
               convex_set add smul V /\
               x IN V /\
               V SUBSET U /\
               open_sets W /\
               x IN W /\
               W SUBSET V in
   let is_compact =
     \(open_sets:(A->bool)->bool) (s:A->bool).
       !C:(A->bool)->bool.
         (!U:A->bool. U IN C ==> open_sets U) /\
         s SUBSET UNIONS C
         ==> ?D:(A->bool)->bool.
               D SUBSET C /\
               FINITE D /\
               s SUBSET UNIONS D in
   let topological_closure =
     \(open_sets:(A->bool)->bool) (s:A->bool).
       {x:A |
          !U:A->bool.
            open_sets U /\ x IN U
            ==> ~(U INTER s = {})} in
   let convex_hull =
     \(add:A->A->A) (smul:real->A->A) (s:A->bool).
       INTERS
         {t:A->bool |
            convex_set add smul t /\ s SUBSET t} in
   let extreme_points =
     \(add:A->A->A) (smul:real->A->A) (s:A->bool).
       {x:A |
          x IN s /\
          !y z:A. !a b:real.
            y IN s /\
            z IN s /\
            &0 < a /\
            &0 < b /\
            a + b = &1 /\
            x = add (smul a y) (smul b z)
            ==> y = x /\ z = x} in
   !zero:A.
   !add:A->A->A.
   !neg:A->A.
   !smul:real->A->A.
   !open_sets:(A->bool)->bool.
   !s:A->bool.
     is_topology open_sets /\
     is_hausdorff open_sets /\
     real_vector_space zero add neg smul /\
     is_topological_add_group add neg open_sets /\
     has_continuous_smul smul open_sets /\
     is_locally_convex add smul open_sets /\
     is_compact open_sets s /\
     convex_set add smul s
     ==> topological_closure open_sets
           (convex_hull add smul
             (extreme_points add smul s)) = s`;;
