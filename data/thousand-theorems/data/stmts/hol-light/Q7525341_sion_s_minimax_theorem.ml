(*
  Statement-only formalization of Thousand Theorems corpus artifact Q7525341
  (thousand-theorems__hol-light__Q7525341), "Sion's minimax theorem": for a
  compact convex subset X and a convex subset Y of real topological vector
  spaces, a lower-semicontinuous quasiconvex / upper-semicontinuous
  quasiconcave function into a densely ordered linear order has equal
  supplied infimum-of-suprema and supremum-of-infima. This file contains no
  proof.
*)

let Q7525341_SION_MINIMAX_THEOREM =
 `let strict =
    \(le:C->C->bool) (a:C) (b:C).
      le a b /\ ~(a = b) in
  let is_linear_order =
    \(le:C->C->bool).
      (!a:C. le a a) /\
      (!a b:C. le a b /\ le b a ==> a = b) /\
      (!a b c:C. le a b /\ le b c ==> le a c) /\
      (!a b:C. le a b \/ le b a) in
  let is_densely_ordered =
    \(le:C->C->bool).
      !a b:C.
        strict le a b
        ==> ?c:C. strict le a c /\ strict le c b in
  let is_topology_E =
    \(openE:(A->bool)->bool).
      openE {} /\
      openE (UNIV:A->bool) /\
      (!family:(A->bool)->bool.
         (!u:A->bool. u IN family ==> openE u)
         ==> openE (UNIONS family)) /\
      (!u v:A->bool.
         openE u /\ openE v ==> openE (u INTER v)) in
  let is_topology_F =
    \(openF:(B->bool)->bool).
      openF {} /\
      openF (UNIV:B->bool) /\
      (!family:(B->bool)->bool.
         (!u:B->bool. u IN family ==> openF u)
         ==> openF (UNIONS family)) /\
      (!u v:B->bool.
         openF u /\ openF v ==> openF (u INTER v)) in
  let real_vector_space_E =
    \(zeroE:A) (addE:A->A->A) (negE:A->A)
     (smulE:real->A->A).
      (!x y z:A. addE x (addE y z) = addE (addE x y) z) /\
      (!x y:A. addE x y = addE y x) /\
      (!x:A. addE zeroE x = x) /\
      (!x:A. addE (negE x) x = zeroE) /\
      (!x:A. smulE (&1) x = x) /\
      (!a b:real. !x:A.
         smulE (a * b) x = smulE a (smulE b x)) /\
      (!a b:real. !x:A.
         smulE (a + b) x = addE (smulE a x) (smulE b x)) /\
      (!a:real. !x y:A.
         smulE a (addE x y) = addE (smulE a x) (smulE a y)) /\
      (!x:A. smulE (&0) x = zeroE) /\
      (!a:real. smulE a zeroE = zeroE) in
  let real_vector_space_F =
    \(zeroF:B) (addF:B->B->B) (negF:B->B)
     (smulF:real->B->B).
      (!x y z:B. addF x (addF y z) = addF (addF x y) z) /\
      (!x y:B. addF x y = addF y x) /\
      (!x:B. addF zeroF x = x) /\
      (!x:B. addF (negF x) x = zeroF) /\
      (!x:B. smulF (&1) x = x) /\
      (!a b:real. !x:B.
         smulF (a * b) x = smulF a (smulF b x)) /\
      (!a b:real. !x:B.
         smulF (a + b) x = addF (smulF a x) (smulF b x)) /\
      (!a:real. !x y:B.
         smulF a (addF x y) = addF (smulF a x) (smulF a y)) /\
      (!x:B. smulF (&0) x = zeroF) /\
      (!a:real. smulF a zeroF = zeroF) in
  let is_topological_add_group_E =
    \(addE:A->A->A) (negE:A->A)
     (openE:(A->bool)->bool).
      (!x y:A. !u:A->bool.
         openE u /\ addE x y IN u
         ==> ?v w:A->bool.
               openE v /\
               openE w /\
               x IN v /\
               y IN w /\
               (!x' y':A.
                  x' IN v /\ y' IN w ==> addE x' y' IN u)) /\
      (!x:A. !u:A->bool.
         openE u /\ negE x IN u
         ==> ?v:A->bool.
               openE v /\
               x IN v /\
               (!x':A. x' IN v ==> negE x' IN u)) in
  let is_topological_add_group_F =
    \(addF:B->B->B) (negF:B->B)
     (openF:(B->bool)->bool).
      (!x y:B. !u:B->bool.
         openF u /\ addF x y IN u
         ==> ?v w:B->bool.
               openF v /\
               openF w /\
               x IN v /\
               y IN w /\
               (!x' y':B.
                  x' IN v /\ y' IN w ==> addF x' y' IN u)) /\
      (!x:B. !u:B->bool.
         openF u /\ negF x IN u
         ==> ?v:B->bool.
               openF v /\
               x IN v /\
               (!x':B. x' IN v ==> negF x' IN u)) in
  let has_continuous_smul_E =
    \(smulE:real->A->A) (openE:(A->bool)->bool).
      !a:real. !x:A. !u:A->bool.
        openE u /\ smulE a x IN u
        ==> ?epsilon:real. ?v:A->bool.
              &0 < epsilon /\
              openE v /\
              x IN v /\
              (!b:real. !y:A.
                 abs(b - a) < epsilon /\ y IN v
                 ==> smulE b y IN u) in
  let has_continuous_smul_F =
    \(smulF:real->B->B) (openF:(B->bool)->bool).
      !a:real. !x:B. !u:B->bool.
        openF u /\ smulF a x IN u
        ==> ?epsilon:real. ?v:B->bool.
              &0 < epsilon /\
              openF v /\
              x IN v /\
              (!b:real. !y:B.
                 abs(b - a) < epsilon /\ y IN v
                 ==> smulF b y IN u) in
  let is_compact_E =
    \(openE:(A->bool)->bool) (s:A->bool).
      !cover:(A->bool)->bool.
        (!u:A->bool. u IN cover ==> openE u) /\
        s SUBSET UNIONS cover
        ==> ?subcover:(A->bool)->bool.
              subcover SUBSET cover /\
              FINITE subcover /\
              s SUBSET UNIONS subcover in
  let convex_E =
    \(addE:A->A->A) (smulE:real->A->A) (s:A->bool).
      !x y:A. !a b:real.
        x IN s /\
        y IN s /\
        &0 <= a /\
        &0 <= b /\
        a + b = &1
        ==> addE (smulE a x) (smulE b y) IN s in
  let convex_F =
    \(addF:B->B->B) (smulF:real->B->B) (s:B->bool).
      !x y:B. !a b:real.
        x IN s /\
        y IN s /\
        &0 <= a /\
        &0 <= b /\
        a + b = &1
        ==> addF (smulF a x) (smulF b y) IN s in
  let lower_semicontinuous_on_E =
    \(le:C->C->bool) (openE:(A->bool)->bool)
     (s:A->bool) (g:A->C).
      !b:C.
        ?u:A->bool.
          openE u /\
          (!x:A.
             x IN s
             ==> (strict le b (g x) <=> x IN u)) in
  let upper_semicontinuous_on_F =
    \(le:C->C->bool) (openF:(B->bool)->bool)
     (s:B->bool) (g:B->C).
      !b:C.
        ?u:B->bool.
          openF u /\
          (!y:B.
             y IN s
             ==> (strict le (g y) b <=> y IN u)) in
  let quasiconvex_on_E =
    \(le:C->C->bool) (addE:A->A->A) (smulE:real->A->A)
     (s:A->bool) (g:A->C).
      !r:C.
        convex_E addE smulE
          {x:A | x IN s /\ le (g x) r} in
  let quasiconcave_on_F =
    \(le:C->C->bool) (addF:B->B->B) (smulF:real->B->B)
     (s:B->bool) (g:B->C).
      !r:C.
        convex_F addF smulF
          {y:B | y IN s /\ le r (g y)} in
  let is_lub =
    \(le:C->C->bool) (s:C->bool) (u:C).
      (!x:C. x IN s ==> le x u) /\
      (!v:C. (!x:C. x IN s ==> le x v) ==> le u v) in
  let is_glb =
    \(le:C->C->bool) (s:C->bool) (l:C).
      (!x:C. x IN s ==> le l x) /\
      (!v:C. (!x:C. x IN s ==> le v x) ==> le v l) in
  !le:C->C->bool.
  !zeroE:A.
  !addE:A->A->A.
  !negE:A->A.
  !smulE:real->A->A.
  !openE:(A->bool)->bool.
  !zeroF:B.
  !addF:B->B->B.
  !negF:B->B.
  !smulF:real->B->B.
  !openF:(B->bool)->bool.
  !X:A->bool.
  !Y:B->bool.
  !f:A->B->C.
  !sup_y:A->C.
  !inf_sup:C.
  !inf_x:B->C.
  !sup_inf:C.
    is_linear_order le /\
    is_densely_ordered le /\
    is_topology_E openE /\
    is_topology_F openF /\
    real_vector_space_E zeroE addE negE smulE /\
    real_vector_space_F zeroF addF negF smulF /\
    is_topological_add_group_E addE negE openE /\
    is_topological_add_group_F addF negF openF /\
    has_continuous_smul_E smulE openE /\
    has_continuous_smul_F smulF openF /\
    (?x:A. x IN X) /\
    convex_E addE smulE X /\
    convex_F addF smulF Y /\
    is_compact_E openE X /\
    (!y:B.
       y IN Y
       ==> lower_semicontinuous_on_E le openE X (\x:A. f x y)) /\
    (!y:B.
       y IN Y
       ==> quasiconvex_on_E le addE smulE X (\x:A. f x y)) /\
    (!x:A.
       x IN X
       ==> upper_semicontinuous_on_F le openF Y (f x)) /\
    (!x:A.
       x IN X
       ==> quasiconcave_on_F le addF smulF Y (f x)) /\
    (!x:A.
       x IN X
       ==> is_lub le
             {v:C | ?y:B. y IN Y /\ v = f x y}
             (sup_y x)) /\
    is_glb le
      {v:C | ?x:A. x IN X /\ v = sup_y x}
      inf_sup /\
    (!y:B.
       y IN Y
       ==> is_glb le
             {v:C | ?x:A. x IN X /\ v = f x y}
             (inf_x y)) /\
    is_lub le
      {v:C | ?y:B. y IN Y /\ v = inf_x y}
      sup_inf
    ==> inf_sup = sup_inf`;;
