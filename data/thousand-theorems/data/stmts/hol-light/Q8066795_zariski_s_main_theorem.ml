(*
  Statement-only formalization of Thousand Theorems corpus artifact Q8066795
  (thousand-theorems__hol-light__Q8066795), "Zariski's main theorem": a proper
  morphism of schemes whose fiber over a point is finite is finite after
  restriction to some open neighborhood of that point. Schemes and morphisms
  are represented by complete structural records; each total-function
  component of a morphism is canonically fixed outside its mathematical
  dependent domain. This file contains no proof.
*)

let Q8066795_ZARISKIS_MAIN_THEOREM =
  `!identity_morphism.
   !compose_morphism.
   !open_subscheme.
   !morphism_restrict.
   !fiber_product.
   !pullback_fst.
   !pullback_snd.
   !diagonal_morphism.
   let scheme_point = \X. FST X in
   let scheme_open = \X. FST (SND X) in
   let open_member = \X. FST (SND (SND X)) in
   let empty_open = \X. FST (SND (SND (SND X))) in
   let top_open = \X. FST (SND (SND (SND (SND X)))) in
   let open_inter =
     \X. FST (SND (SND (SND (SND (SND X))))) in
   let open_union =
     \X. FST (SND (SND (SND (SND (SND (SND X)))))) in
   let section =
     \X. FST (SND (SND (SND (SND (SND (SND (SND X))))))) in
   let zero_section =
     \X. FST (SND (SND (SND (SND (SND (SND (SND (SND X)))))))) in
   let one_section =
     \X. FST
       (SND (SND (SND (SND (SND (SND (SND (SND (SND X))))))))) in
   let add_section =
     \X. FST
       (SND
         (SND (SND (SND (SND (SND (SND (SND (SND (SND X)))))))))) in
   let mul_section =
     \X. FST
       (SND
         (SND
           (SND (SND (SND (SND (SND (SND (SND (SND (SND X))))))))))) in
   let neg_section =
     \X. FST
       (SND
         (SND
           (SND
             (SND (SND (SND (SND (SND (SND (SND (SND (SND X)))))))))))) in
   let restrict_section =
     \X. FST
       (SND
         (SND
           (SND
             (SND
               (SND (SND (SND (SND (SND (SND (SND (SND (SND X))))))))))))) in
   let point_prime =
     \X. FST
       (SND
         (SND
           (SND
             (SND
               (SND
                 (SND
                   (SND
                     (SND
                       (SND
                         (SND (SND (SND (SND (SND X)))))))))))))) in
   let principal_open =
     \X.
       SND
         (SND
           (SND
             (SND
               (SND
                 (SND
                   (SND
                     (SND
                       (SND
                         (SND
                           (SND (SND (SND (SND (SND X)))))))))))))) in
   let morphism_map = \X Y f. FST f in
   let inverse_open = \X Y f. FST (SND f) in
   let map_section = \X Y f. SND (SND f) in
   let open_le =
     \(X) (U:O) (V:O).
       scheme_open X U /\
       scheme_open X V /\
       !x:P.
         scheme_point X x /\ open_member X U x
         ==> open_member X V x in
   let is_commutative_ring =
     \(X) (U:O).
       section X U (zero_section X U) /\
       section X U (one_section X U) /\
       (!a:R.
          section X U a
          ==> section X U (neg_section X U a)) /\
       (!a b:R.
          section X U a /\ section X U b
          ==> section X U (add_section X U a b) /\
              section X U (mul_section X U a b)) /\
       (!a:R.
          section X U a
          ==> add_section X U (zero_section X U) a = a /\
              add_section X U (neg_section X U a) a =
                zero_section X U /\
              mul_section X U (one_section X U) a = a) /\
       (!a b:R.
          section X U a /\ section X U b
          ==> add_section X U a b = add_section X U b a /\
              mul_section X U a b = mul_section X U b a) /\
       (!a b c:R.
          section X U a /\ section X U b /\ section X U c
          ==> add_section X U a (add_section X U b c) =
                add_section X U (add_section X U a b) c /\
              mul_section X U a (mul_section X U b c) =
                mul_section X U (mul_section X U a b) c /\
              mul_section X U a (add_section X U b c) =
                add_section X U
                  (mul_section X U a b)
                  (mul_section X U a c)) in
   let is_ring_hom =
     \(X) (U:O) (Y) (V:O) (phi:R->R).
       (!a:R. section X U a ==> section Y V (phi a)) /\
       phi (zero_section X U) = zero_section Y V /\
       phi (one_section X U) = one_section Y V /\
       (!a:R.
          section X U a
          ==> phi (neg_section X U a) = neg_section Y V (phi a)) /\
       (!a b:R.
          section X U a /\ section X U b
          ==> phi (add_section X U a b) =
                add_section Y V (phi a) (phi b) /\
              phi (mul_section X U a b) =
                mul_section Y V (phi a) (phi b)) in
   let is_topological_space =
     \(X).
       scheme_open X (empty_open X) /\
       scheme_open X (top_open X) /\
       (!x:P.
          scheme_point X x
          ==> ~(open_member X (empty_open X) x) /\
              open_member X (top_open X) x) /\
       (!U V:O.
          scheme_open X U /\ scheme_open X V
          ==> scheme_open X (open_inter X U V) /\
              (!x:P.
                 scheme_point X x
                 ==> (open_member X (open_inter X U V) x <=>
                      open_member X U x /\ open_member X V x))) /\
       (!family:O->bool.
          (!U:O. family U ==> scheme_open X U)
          ==> scheme_open X (open_union X family) /\
              (!x:P.
                 scheme_point X x
                 ==> (open_member X (open_union X family) x <=>
                      ?U:O. family U /\ open_member X U x))) /\
       (!U V:O.
          scheme_open X U /\ scheme_open X V /\
          (!x:P.
             scheme_point X x
             ==> (open_member X U x <=> open_member X V x))
          ==> U = V) in
   let is_open_cover =
     \(X) (U:O) (family:O->bool).
       scheme_open X U /\
       (!V:O. family V ==> open_le X V U) /\
       (!x:P.
          scheme_point X x /\ open_member X U x
          ==> ?V:O. family V /\ open_member X V x) in
   let is_sheaf_of_rings =
     \(X).
       (!U:O.
          scheme_open X U
          ==> is_commutative_ring X U) /\
       (!U V:O.
          open_le X V U
          ==> is_ring_hom X U X V (restrict_section X U V)) /\
       (!U:O.
          scheme_open X U
          ==> !a:R.
                section X U a
                ==> restrict_section X U U a = a) /\
       (!U V W:O.
          open_le X V U /\ open_le X W V
          ==> !a:R.
                section X U a
                ==> restrict_section X V W
                      (restrict_section X U V a) =
                    restrict_section X U W a) /\
       (!U:O. !family:O->bool. !local_section:O->R.
          is_open_cover X U family /\
          (!V:O.
             family V ==> section X V (local_section V)) /\
          (!V W:O.
             family V /\ family W
             ==> restrict_section X V (open_inter X V W)
                   (local_section V) =
                 restrict_section X W (open_inter X V W)
                   (local_section W))
          ==> ?a:R.
                section X U a /\
                (!V:O.
                   family V
                   ==> restrict_section X U V a = local_section V) /\
                (!b:R.
                   section X U b /\
                   (!V:O.
                      family V
                      ==> restrict_section X U V b = local_section V)
                   ==> b = a)) in
   let is_prime_ideal =
     \(X) (U:O) (p:R->bool).
       (!a:R. p a ==> section X U a) /\
       p (zero_section X U) /\
       ~(p (one_section X U)) /\
       (!a:R.
          p a ==> p (neg_section X U a)) /\
       (!a b:R.
          p a /\ p b ==> p (add_section X U a b)) /\
       (!a b:R.
          section X U a /\ p b
          ==> p (mul_section X U a b)) /\
       (!a b:R.
          section X U a /\ section X U b /\
          p (mul_section X U a b)
          ==> p a \/ p b) in
   let ring_power =
     \(X) (U:O) (a:R) (n:num).
       ITLIST (mul_section X U) (REPLICATE n a)
         (one_section X U) in
   let is_localization_at =
     \(X) (U:O) (V:O) (phi:R->R) (a:R).
       is_ring_hom X U X V phi /\
       (?v:R.
          section X V v /\
          mul_section X V (phi a) v = one_section X V) /\
       (!b:R.
          section X V b
          ==> ?c:R. ?n:num. ?v:R.
                section X U c /\
                section X V v /\
                mul_section X V
                  (ring_power X V (phi a) n) v =
                    one_section X V /\
                b = mul_section X V (phi c) v) /\
       (!c:R.
          section X U c /\ phi c = zero_section X V
          ==> ?n:num.
                mul_section X U
                  (ring_power X U a n) c = zero_section X U) in
   let is_affine_open =
     \(X) (U:O).
       scheme_open X U /\
       (!x:P.
          scheme_point X x /\ open_member X U x
          ==> is_prime_ideal X U (point_prime X U x)) /\
       (!p:R->bool.
          is_prime_ideal X U p
          ==> ?x:P.
                scheme_point X x /\
                open_member X U x /\
                point_prime X U x = p /\
                (!y:P.
                   scheme_point X y /\
                   open_member X U y /\
                   point_prime X U y = p
                   ==> y = x)) /\
       (!a:R.
          section X U a
          ==> open_le X (principal_open X U a) U /\
              (!x:P.
                 scheme_point X x
                 ==> (open_member X (principal_open X U a) x <=>
                      open_member X U x /\ ~(point_prime X U x a))) /\
              is_localization_at
                X U (principal_open X U a)
                (restrict_section X U (principal_open X U a)) a) /\
       (!V:O. !x:P.
          open_le X V U /\
          scheme_point X x /\ open_member X V x
          ==> ?a:R.
                section X U a /\
                open_member X (principal_open X U a) x /\
                open_le X (principal_open X U a) V) in
   let is_scheme =
     \(X).
       is_topological_space X /\
       is_sheaf_of_rings X /\
       (!x:P.
          scheme_point X x
          ==> ?U:O.
                is_affine_open X U /\ open_member X U x) in
   let is_germ_unit =
     \(X) (U:O) (x:P) (a:R).
       scheme_point X x /\
       scheme_open X U /\
       open_member X U x /\
       section X U a /\
       ?V:O. ?b:R.
         open_le X V U /\
         open_member X V x /\
         section X V b /\
         mul_section X V (restrict_section X U V a) b =
           one_section X V in
   let is_scheme_morphism =
     \(X) (Y) (f).
       is_scheme X /\
       is_scheme Y /\
       (!x:P.
          ~(scheme_point X x)
          ==> morphism_map X Y f x = (@z:P. T)) /\
       (!U:O.
          ~(scheme_open Y U)
          ==> inverse_open X Y f U = empty_open X) /\
       (!U:O. !a:R.
          ~(scheme_open Y U /\ section Y U a)
          ==> map_section X Y f U a =
              zero_section X (inverse_open X Y f U)) /\
       (!x:P.
          scheme_point X x
          ==> scheme_point Y (morphism_map X Y f x)) /\
       (!U:O.
          scheme_open Y U
          ==> scheme_open X (inverse_open X Y f U) /\
              (!x:P.
                 scheme_point X x
                 ==> (open_member X (inverse_open X Y f U) x <=>
                      open_member Y U (morphism_map X Y f x))) /\
              is_ring_hom
                Y U X (inverse_open X Y f U)
                (map_section X Y f U)) /\
       (!U V:O.
          open_le Y V U
          ==> !a:R.
                section Y U a
                ==> restrict_section X
                      (inverse_open X Y f U)
                      (inverse_open X Y f V)
                      (map_section X Y f U a) =
                    map_section X Y f V
                      (restrict_section Y U V a)) /\
       (!x:P. !U:O. !a:R.
          scheme_point X x /\
          scheme_open Y U /\
          open_member Y U (morphism_map X Y f x) /\
          section Y U a /\
          is_germ_unit
            X (inverse_open X Y f U) x
            (map_section X Y f U a)
          ==> is_germ_unit
                Y U (morphism_map X Y f x) a) in
   let is_submodule =
     \(X) (U:O) (Y) (V:O) (phi:R->R) (N:R->bool).
       (!b:R. N b ==> section Y V b) /\
       N (zero_section Y V) /\
       (!b:R. N b ==> N (neg_section Y V b)) /\
       (!b c:R.
          N b /\ N c ==> N (add_section Y V b c)) /\
       (!a b:R.
          section X U a /\ N b
          ==> N (mul_section Y V (phi a) b)) in
   let is_finite_module =
     \(X) (U:O) (Y) (V:O) (phi:R->R).
       is_ring_hom X U Y V phi /\
       ?generators:R->bool.
         FINITE generators /\
         (!g:R. generators g ==> section Y V g) /\
         (!N:R->bool.
            is_submodule X U Y V phi N /\
            (!g:R. generators g ==> N g)
            ==> !b:R. section Y V b ==> N b) in
   let is_subalgebra =
     \(X) (U:O) (Y) (V:O) (phi:R->R) (A:R->bool).
       (!b:R. A b ==> section Y V b) /\
       (!a:R. section X U a ==> A (phi a)) /\
       A (zero_section Y V) /\
       A (one_section Y V) /\
       (!b:R. A b ==> A (neg_section Y V b)) /\
       (!b c:R.
          A b /\ A c
          ==> A (add_section Y V b c) /\
              A (mul_section Y V b c)) in
   let is_finite_type_algebra =
     \(X) (U:O) (Y) (V:O) (phi:R->R).
       is_ring_hom X U Y V phi /\
       ?generators:R->bool.
         FINITE generators /\
         (!g:R. generators g ==> section Y V g) /\
         (!A:R->bool.
            is_subalgebra X U Y V phi A /\
            (!g:R. generators g ==> A g)
            ==> !b:R. section Y V b ==> A b) in
   let is_closed_subset =
     \(X) (C:P->bool).
       (!x:P. C x ==> scheme_point X x) /\
       ?U:O.
         scheme_open X U /\
         !x:P.
           scheme_point X x
           ==> (C x <=> ~(open_member X U x)) in
   let is_closed_map =
     \(X) (Y) (f).
       is_scheme_morphism X Y f /\
       !C:P->bool.
         is_closed_subset X C
         ==> is_closed_subset Y
               (\y:P.
                  scheme_point Y y /\
                  ?x:P.
                    scheme_point X x /\
                    C x /\
                    morphism_map X Y f x = y) in
   let is_closed_immersion =
     \(X) (Y) (f).
       is_scheme_morphism X Y f /\
       !U:O.
         is_affine_open Y U
         ==> is_affine_open X (inverse_open X Y f U) /\
             (!b:R.
                section X (inverse_open X Y f U) b
                ==> ?a:R.
                      section Y U a /\
                      map_section X Y f U a = b) in
   let is_category_of_schemes =
     (T /\
     (!X.
        is_scheme X
        ==> is_scheme_morphism X X (identity_morphism X) /\
            (!x:P.
               scheme_point X x
               ==> morphism_map X X (identity_morphism X) x = x) /\
            (!U:O.
               scheme_open X U
               ==> inverse_open X X (identity_morphism X) U = U /\
                   (!a:R.
                      section X U a
                      ==> map_section X X (identity_morphism X) U a =
                          a))) /\
     (!X Y Z. !f g.
        is_scheme_morphism X Y f /\
        is_scheme_morphism Y Z g
        ==> is_scheme_morphism X Z
              (compose_morphism X Y Z f g) /\
            (!x:P.
               scheme_point X x
               ==> morphism_map X Z
                     (compose_morphism X Y Z f g) x =
                   morphism_map Y Z g
                     (morphism_map X Y f x)) /\
            (!U:O.
               scheme_open Z U
               ==> inverse_open X Z
                     (compose_morphism X Y Z f g) U =
                   inverse_open X Y f (inverse_open Y Z g U) /\
                   (!a:R.
                      section Z U a
                      ==> map_section X Z
                            (compose_morphism X Y Z f g) U a =
                          map_section X Y f
                            (inverse_open Y Z g U)
                            (map_section Y Z g U a)))) /\
     (!W X Y Z. !f g h.
        is_scheme_morphism W X f /\
        is_scheme_morphism X Y g /\
        is_scheme_morphism Y Z h
        ==> compose_morphism W Y Z
              (compose_morphism W X Y f g) h =
            compose_morphism W X Z f
              (compose_morphism X Y Z g h)) /\
     (!X Y. !f.
        is_scheme_morphism X Y f
        ==> compose_morphism X X Y (identity_morphism X) f = f /\
            compose_morphism X Y Y f (identity_morphism Y) = f) /\
     (!X Y. !f g.
        is_scheme_morphism X Y f /\
        is_scheme_morphism X Y g /\
        (!x:P.
           scheme_point X x
           ==> morphism_map X Y f x = morphism_map X Y g x) /\
        (!U:O. !a:R.
           scheme_open Y U /\ section Y U a
           ==> map_section X Y f U a = map_section X Y g U a)
        ==> f = g)) in
   let has_pullbacks =
     (!X Z Y. !f g.
       is_scheme_morphism X Y f /\
       is_scheme_morphism Z Y g
       ==> let W = fiber_product X Z Y f g in
           let p = pullback_fst X Z Y f g in
           let q = pullback_snd X Z Y f g in
             is_scheme W /\
             is_scheme_morphism W X p /\
             is_scheme_morphism W Z q /\
             compose_morphism W X Y p f =
               compose_morphism W Z Y q g /\
             (!A. !a b.
                is_scheme_morphism A X a /\
                is_scheme_morphism A Z b /\
                compose_morphism A X Y a f =
                  compose_morphism A Z Y b g
                ==> ?u.
                      is_scheme_morphism A W u /\
                      compose_morphism A W X u p = a /\
                      compose_morphism A W Z u q = b /\
                      (!v.
                         is_scheme_morphism A W v /\
                         compose_morphism A W X v p = a /\
                         compose_morphism A W Z v q = b
                         ==> v = u))) in
   let has_diagonals =
     (!X Y. !f.
       is_scheme_morphism X Y f
       ==> let W = fiber_product X X Y f f in
           let p = pullback_fst X X Y f f in
           let q = pullback_snd X X Y f f in
           let d = diagonal_morphism X Y f in
             is_scheme_morphism X W d /\
             compose_morphism X W X d p = identity_morphism X /\
             compose_morphism X W X d q = identity_morphism X) in
   let has_open_subschemes =
     (!X. !U:O.
       is_scheme X /\ scheme_open X U
       ==> let XU = open_subscheme X U in
             is_scheme XU /\
             (!x:P.
                scheme_point XU x <=>
                scheme_point X x /\ open_member X U x) /\
             (!V:O.
                scheme_open XU V <=>
                open_le X V U) /\
             (!V:O. !x:P.
                scheme_open XU V /\ scheme_point XU x
                ==> (open_member XU V x <=> open_member X V x)) /\
             empty_open XU = empty_open X /\
             top_open XU = U /\
             (!V W:O.
                scheme_open XU V /\ scheme_open XU W
                ==> open_inter XU V W = open_inter X V W) /\
             (!family:O->bool.
                (!V:O. family V ==> scheme_open XU V)
                ==> open_union XU family = open_union X family) /\
             (!V:O. !a:R.
                scheme_open XU V
                ==> (section XU V a <=> section X V a)) /\
             (!V:O.
                scheme_open XU V
                ==> zero_section XU V = zero_section X V /\
                    one_section XU V = one_section X V /\
                    add_section XU V = add_section X V /\
                    mul_section XU V = mul_section X V /\
                    neg_section XU V = neg_section X V /\
                    point_prime XU V = point_prime X V) /\
             (!V W:O.
                open_le XU W V
                ==> restrict_section XU V W =
                    restrict_section X V W) /\
             (!V:O. !a:R.
                scheme_open XU V /\ section XU V a
                ==> principal_open XU V a =
                    principal_open X V a)) in
   let has_morphism_restrictions =
     (!X Y. !f. !U:O.
       is_scheme_morphism X Y f /\ scheme_open Y U
       ==> let XU =
             open_subscheme X (inverse_open X Y f U) in
           let YU = open_subscheme Y U in
           let r = morphism_restrict X Y f U in
             is_scheme_morphism XU YU r /\
             (!x:P.
                scheme_point XU x
                ==> morphism_map XU YU r x =
                    morphism_map X Y f x) /\
             (!V:O.
                scheme_open YU V
                ==> inverse_open XU YU r V =
                    inverse_open X Y f V /\
                    (!a:R.
                       section YU V a
                       ==> map_section XU YU r V a =
                           map_section X Y f V a))) in
   let is_locally_of_finite_type =
     \(X) (Y) (f).
       is_scheme_morphism X Y f /\
       !U V:O.
         is_affine_open Y U /\
         is_affine_open X V /\
         open_le X V (inverse_open X Y f U)
         ==> is_finite_type_algebra
               Y U X V
               (\a:R.
                  restrict_section X
                    (inverse_open X Y f U) V
                    (map_section X Y f U a)) in
   let is_universally_closed =
     \(X) (Y) (f).
       is_scheme_morphism X Y f /\
       !Z. !g.
         is_scheme_morphism Z Y g
         ==> is_closed_map
               (fiber_product X Z Y f g) Z
               (pullback_snd X Z Y f g) in
   let is_separated =
     \(X) (Y) (f).
       is_scheme_morphism X Y f /\
       is_closed_immersion
         X (fiber_product X X Y f f)
         (diagonal_morphism X Y f) in
   let is_proper_morphism =
     \(X) (Y) (f).
       is_separated X Y f /\
       is_universally_closed X Y f /\
       is_locally_of_finite_type X Y f in
   let is_finite_morphism =
     \(X) (Y) (f).
       is_scheme_morphism X Y f /\
       !U:O.
         is_affine_open Y U
         ==> is_affine_open X (inverse_open X Y f U) /\
             is_finite_module
               Y U X (inverse_open X Y f U)
               (map_section X Y f U) in
   let is_scheme_geometry =
     (is_category_of_schemes /\
     has_pullbacks /\
     has_diagonals /\
     has_open_subschemes /\
     has_morphism_restrictions) in
   !X Y. !f. !y:P.
     is_scheme_geometry /\
     is_scheme X /\
     is_scheme Y /\
     is_scheme_morphism X Y f /\
     scheme_point Y y /\
     is_proper_morphism X Y f /\
     FINITE
       {x:P |
          scheme_point X x /\ morphism_map X Y f x = y}
     ==> ?V:O.
           scheme_open Y V /\
           open_member Y V y /\
           is_finite_morphism
             (open_subscheme X (inverse_open X Y f V))
             (open_subscheme Y V)
             (morphism_restrict X Y f V)`;;
