(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1148215,
  "Mitchell's embedding theorem": every abelian category admits a full and
  faithful functor into modules over a ring that preserves finite limits and
  finite colimits. This file contains no proof.

  HOL cannot existentially quantify over carrier types. The ring is therefore
  coded in a powerset of the object, arrow, and natural-number data, while
  module vectors use one further powerset. These two levels retain the carrier
  freedom needed by the standard small-category construction.
*)

let Q1148215_MITCHELL_S_EMBEDDING_THEOREM =
  `let hom =
     \(objects:O->bool) (morphisms:M->bool) (dom:M->O) (cod:M->O)
      (x:O) (y:O) (f:M).
       objects x /\ objects y /\ morphisms f /\ dom f = x /\ cod f = y in
   let is_category =
     \(objects:O->bool) (morphisms:M->bool) (dom:M->O) (cod:M->O)
      (identity:O->M) (compose:M->M->M).
       (!f:M.
          morphisms f
          ==> objects (dom f) /\ objects (cod f)) /\
       (!x:O.
          objects x
          ==> hom objects morphisms dom cod x x (identity x)) /\
       (!x y z:O. !f g:M.
          hom objects morphisms dom cod x y f /\
          hom objects morphisms dom cod y z g
          ==> hom objects morphisms dom cod x z (compose g f)) /\
       (!x y:O. !f:M.
          hom objects morphisms dom cod x y f
          ==> compose (identity y) f = f /\
              compose f (identity x) = f) /\
       (!w x y z:O. !f g h:M.
          hom objects morphisms dom cod w x f /\
          hom objects morphisms dom cod x y g /\
          hom objects morphisms dom cod y z h
          ==> compose h (compose g f) = compose (compose h g) f) in
   let is_preadditive_category =
     \(objects:O->bool) (morphisms:M->bool) (dom:M->O) (cod:M->O)
      (identity:O->M) (compose:M->M->M)
      (zero:O->O->M) (add:M->M->M) (neg:M->M).
       is_category objects morphisms dom cod identity compose /\
       (!x y:O.
          objects x /\ objects y
          ==> hom objects morphisms dom cod x y (zero x y)) /\
       (!x y:O. !f g:M.
          hom objects morphisms dom cod x y f /\
          hom objects morphisms dom cod x y g
          ==> hom objects morphisms dom cod x y (add f g) /\
              add f g = add g f) /\
       (!x y:O. !f g h:M.
          hom objects morphisms dom cod x y f /\
          hom objects morphisms dom cod x y g /\
          hom objects morphisms dom cod x y h
          ==> add f (add g h) = add (add f g) h) /\
       (!x y:O. !f:M.
          hom objects morphisms dom cod x y f
          ==> add (zero x y) f = f /\
              hom objects morphisms dom cod x y (neg f) /\
              add (neg f) f = zero x y) /\
       (!w x y:O. !f g:M.
          hom objects morphisms dom cod w x f /\
          hom objects morphisms dom cod x y g
          ==> compose (zero x y) f = zero w y /\
              compose g (zero w x) = zero w y) /\
       (!w x y:O. !f g h:M.
          hom objects morphisms dom cod w x f /\
          hom objects morphisms dom cod w x g /\
          hom objects morphisms dom cod x y h
          ==> compose h (add f g) =
              add (compose h f) (compose h g)) /\
       (!w x y:O. !f g h:M.
          hom objects morphisms dom cod w x f /\
          hom objects morphisms dom cod x y g /\
          hom objects morphisms dom cod x y h
          ==> compose (add g h) f =
              add (compose g f) (compose h f)) in
   let is_zero_object =
     \(objects:O->bool) (morphisms:M->bool) (dom:M->O) (cod:M->O)
      (z:O).
       objects z /\
       (!x:O.
          objects x
          ==> (?f:M.
                 hom objects morphisms dom cod x z f /\
                 !g:M. hom objects morphisms dom cod x z g ==> g = f) /\
              (?f:M.
                 hom objects morphisms dom cod z x f /\
                 !g:M. hom objects morphisms dom cod z x g ==> g = f)) in
   let is_biproduct =
     \(objects:O->bool) (morphisms:M->bool) (dom:M->O) (cod:M->O)
      (identity:O->M) (compose:M->M->M)
      (zero:O->O->M) (add:M->M->M)
      (x:O) (y:O) (p:O) (i1:M) (i2:M) (p1:M) (p2:M).
       hom objects morphisms dom cod x p i1 /\
       hom objects morphisms dom cod y p i2 /\
       hom objects morphisms dom cod p x p1 /\
       hom objects morphisms dom cod p y p2 /\
       compose p1 i1 = identity x /\
       compose p2 i2 = identity y /\
       compose p1 i2 = zero y x /\
       compose p2 i1 = zero x y /\
       add (compose i1 p1) (compose i2 p2) = identity p in
   let is_kernel =
     \(objects:O->bool) (morphisms:M->bool) (dom:M->O) (cod:M->O)
      (compose:M->M->M) (zero:O->O->M)
      (kobject:O) (a:O) (b:O) (k:M) (f:M).
       hom objects morphisms dom cod kobject a k /\
       hom objects morphisms dom cod a b f /\
       compose f k = zero kobject b /\
       (!tobject:O. !t:M.
          hom objects morphisms dom cod tobject a t /\
          compose f t = zero tobject b
          ==> ?u:M.
                hom objects morphisms dom cod tobject kobject u /\
                compose k u = t /\
                !v:M.
                  hom objects morphisms dom cod tobject kobject v /\
                  compose k v = t
                  ==> v = u) in
   let is_cokernel =
     \(objects:O->bool) (morphisms:M->bool) (dom:M->O) (cod:M->O)
      (compose:M->M->M) (zero:O->O->M)
      (a:O) (b:O) (qobject:O) (f:M) (q:M).
       hom objects morphisms dom cod a b f /\
       hom objects morphisms dom cod b qobject q /\
       compose q f = zero a qobject /\
       (!tobject:O. !t:M.
          hom objects morphisms dom cod b tobject t /\
          compose t f = zero a tobject
          ==> ?u:M.
                hom objects morphisms dom cod qobject tobject u /\
                compose u q = t /\
                !v:M.
                  hom objects morphisms dom cod qobject tobject v /\
                  compose v q = t
                  ==> v = u) in
   let is_monic =
     \(objects:O->bool) (morphisms:M->bool) (dom:M->O) (cod:M->O)
      (compose:M->M->M) (x:O) (y:O) (f:M).
       hom objects morphisms dom cod x y f /\
       !z:O. !g h:M.
         hom objects morphisms dom cod z x g /\
         hom objects morphisms dom cod z x h /\
         compose f g = compose f h
         ==> g = h in
   let is_epic =
     \(objects:O->bool) (morphisms:M->bool) (dom:M->O) (cod:M->O)
      (compose:M->M->M) (x:O) (y:O) (f:M).
       hom objects morphisms dom cod x y f /\
       !z:O. !g h:M.
         hom objects morphisms dom cod y z g /\
         hom objects morphisms dom cod y z h /\
         compose g f = compose h f
         ==> g = h in
   let is_abelian_category =
     \(objects:O->bool) (morphisms:M->bool) (dom:M->O) (cod:M->O)
      (identity:O->M) (compose:M->M->M)
      (zero:O->O->M) (add:M->M->M) (neg:M->M).
       is_preadditive_category objects morphisms dom cod identity compose
         zero add neg /\
       (?z:O. is_zero_object objects morphisms dom cod z) /\
       (!x y:O.
          objects x /\ objects y
          ==> ?p:O. ?i1 i2 p1 p2:M.
                objects p /\
                is_biproduct objects morphisms dom cod identity compose
                  zero add x y p i1 i2 p1 p2) /\
       (!a b:O. !f:M.
          hom objects morphisms dom cod a b f
          ==> ?kobject:O. ?k:M.
                objects kobject /\
                is_kernel objects morphisms dom cod compose zero
                  kobject a b k f) /\
       (!a b:O. !f:M.
          hom objects morphisms dom cod a b f
          ==> ?qobject:O. ?q:M.
                objects qobject /\
                is_cokernel objects morphisms dom cod compose zero
                  a b qobject f q) /\
       (!x y:O. !f:M.
          is_monic objects morphisms dom cod compose x y f
          ==> ?z:O. ?g:M.
                objects z /\
                is_kernel objects morphisms dom cod compose zero
                  x y z f g) /\
       (!x y:O. !f:M.
          is_epic objects morphisms dom cod compose x y f
          ==> ?z:O. ?g:M.
                objects z /\
                is_cokernel objects morphisms dom cod compose zero
                  z x y g f) in
   let is_ring =
     \(carrier:((num#O#M)->bool)->bool)
      (rzero:(num#O#M)->bool) (rone:(num#O#M)->bool)
      (radd:((num#O#M)->bool)->((num#O#M)->bool)->((num#O#M)->bool))
      (rmul:((num#O#M)->bool)->((num#O#M)->bool)->((num#O#M)->bool))
      (rneg:((num#O#M)->bool)->((num#O#M)->bool)).
       carrier rzero /\ carrier rone /\
       (!r s:(num#O#M)->bool.
          carrier r /\ carrier s
          ==> carrier (radd r s) /\
              carrier (rmul r s)) /\
       (!r:(num#O#M)->bool.
          carrier r
          ==> carrier (rneg r) /\
              radd rzero r = r /\
              radd (rneg r) r = rzero /\
              rmul rone r = r /\
              rmul r rone = r) /\
       (!r s:(num#O#M)->bool.
          carrier r /\ carrier s
          ==> radd r s = radd s r) /\
       (!r s t:(num#O#M)->bool.
          carrier r /\ carrier s /\ carrier t
          ==> radd r (radd s t) = radd (radd r s) t /\
              rmul r (rmul s t) = rmul (rmul r s) t /\
              rmul r (radd s t) = radd (rmul r s) (rmul r t) /\
              rmul (radd r s) t = radd (rmul r t) (rmul s t)) in
   let is_module =
     \(ring_carrier:((num#O#M)->bool)->bool)
      (rone:(num#O#M)->bool)
      (radd:((num#O#M)->bool)->((num#O#M)->bool)->((num#O#M)->bool))
      (rmul:((num#O#M)->bool)->((num#O#M)->bool)->((num#O#M)->bool))
      (module_carrier:(((num#O#M)->bool)->bool)->bool)
      (mzero:((num#O#M)->bool)->bool)
      (madd:(((num#O#M)->bool)->bool)->
            (((num#O#M)->bool)->bool)->(((num#O#M)->bool)->bool))
      (mneg:(((num#O#M)->bool)->bool)->(((num#O#M)->bool)->bool))
      (smul:((num#O#M)->bool)->
            (((num#O#M)->bool)->bool)->(((num#O#M)->bool)->bool)).
       module_carrier mzero /\
       (!u v:((num#O#M)->bool)->bool.
          module_carrier u /\ module_carrier v
          ==> module_carrier (madd u v) /\
              madd u v = madd v u) /\
       (!u v w:((num#O#M)->bool)->bool.
          module_carrier u /\ module_carrier v /\ module_carrier w
          ==> madd u (madd v w) = madd (madd u v) w) /\
       (!u:((num#O#M)->bool)->bool.
          module_carrier u
          ==> module_carrier (mneg u) /\
              madd mzero u = u /\
              madd (mneg u) u = mzero) /\
       (!r:(num#O#M)->bool. !u:((num#O#M)->bool)->bool.
          ring_carrier r /\ module_carrier u
          ==> module_carrier (smul r u)) /\
       (!r s:(num#O#M)->bool. !u v:((num#O#M)->bool)->bool.
          ring_carrier r /\ ring_carrier s /\
          module_carrier u /\ module_carrier v
          ==> smul r (madd u v) = madd (smul r u) (smul r v) /\
              smul (radd r s) u = madd (smul r u) (smul s u) /\
              smul (rmul r s) u = smul r (smul s u) /\
              smul rone u = u) in
   let is_linear =
     \(ring_carrier:((num#O#M)->bool)->bool)
      (source_carrier:(((num#O#M)->bool)->bool)->bool)
      (source_zero:((num#O#M)->bool)->bool)
      (source_add:(((num#O#M)->bool)->bool)->
                  (((num#O#M)->bool)->bool)->(((num#O#M)->bool)->bool))
      (source_smul:((num#O#M)->bool)->
                   (((num#O#M)->bool)->bool)->(((num#O#M)->bool)->bool))
      (target_carrier:(((num#O#M)->bool)->bool)->bool)
      (target_zero:((num#O#M)->bool)->bool)
      (target_add:(((num#O#M)->bool)->bool)->
                  (((num#O#M)->bool)->bool)->(((num#O#M)->bool)->bool))
      (target_smul:((num#O#M)->bool)->
                   (((num#O#M)->bool)->bool)->(((num#O#M)->bool)->bool))
      (linear:(((num#O#M)->bool)->bool)->(((num#O#M)->bool)->bool)).
       (!u:((num#O#M)->bool)->bool.
          source_carrier u ==> target_carrier (linear u)) /\
       linear source_zero = target_zero /\
       (!u v:((num#O#M)->bool)->bool.
          source_carrier u /\ source_carrier v
          ==> linear (source_add u v) =
              target_add (linear u) (linear v)) /\
       (!r:(num#O#M)->bool. !u:((num#O#M)->bool)->bool.
          ring_carrier r /\ source_carrier u
          ==> linear (source_smul r u) =
              target_smul r (linear u)) in
   !objects:O->bool. !morphisms:M->bool.
   !dom:M->O. !cod:M->O. !identity:O->M. !compose:M->M->M.
   !zero:O->O->M. !add:M->M->M. !neg:M->M.
     is_abelian_category objects morphisms dom cod identity compose
       zero add neg
     ==> ?ring_carrier:((num#O#M)->bool)->bool.
         ?rzero rone:(num#O#M)->bool.
         ?radd rmul:
            ((num#O#M)->bool)->((num#O#M)->bool)->((num#O#M)->bool).
         ?rneg:((num#O#M)->bool)->((num#O#M)->bool).
         ?module_carrier:O->(((num#O#M)->bool)->bool)->bool.
         ?module_zero:O->((num#O#M)->bool)->bool.
         ?module_add:
            O->(((num#O#M)->bool)->bool)->
               (((num#O#M)->bool)->bool)->(((num#O#M)->bool)->bool).
         ?module_neg:
            O->(((num#O#M)->bool)->bool)->(((num#O#M)->bool)->bool).
         ?module_smul:
            O->((num#O#M)->bool)->
               (((num#O#M)->bool)->bool)->(((num#O#M)->bool)->bool).
         ?functor_morphism:
            M->(((num#O#M)->bool)->bool)->(((num#O#M)->bool)->bool).
           is_ring ring_carrier rzero rone radd rmul rneg /\
           (!x:O.
              objects x
              ==> is_module ring_carrier rone radd rmul
                    (module_carrier x) (module_zero x)
                    (module_add x) (module_neg x) (module_smul x)) /\
           (!x y:O. !f:M.
              hom objects morphisms dom cod x y f
              ==> is_linear ring_carrier
                    (module_carrier x) (module_zero x)
                    (module_add x) (module_smul x)
                    (module_carrier y) (module_zero y)
                    (module_add y) (module_smul y)
                    (functor_morphism f)) /\
           (!x:O. !u:((num#O#M)->bool)->bool.
              objects x /\ module_carrier x u
              ==> functor_morphism (identity x) u = u) /\
           (!x y z:O. !f g:M. !u:((num#O#M)->bool)->bool.
              hom objects morphisms dom cod x y f /\
              hom objects morphisms dom cod y z g /\
              module_carrier x u
              ==> functor_morphism (compose g f) u =
                  functor_morphism g (functor_morphism f u)) /\
           (!x y:O. !u:((num#O#M)->bool)->bool.
              objects x /\ objects y /\ module_carrier x u
              ==> functor_morphism (zero x y) u = module_zero y) /\
           (!x y:O. !f g:M. !u:((num#O#M)->bool)->bool.
              hom objects morphisms dom cod x y f /\
              hom objects morphisms dom cod x y g /\
              module_carrier x u
              ==> functor_morphism (add f g) u =
                  module_add y
                    (functor_morphism f u) (functor_morphism g u)) /\
           (!x y:O.
              objects x /\ objects y
              ==> !linear:
                    (((num#O#M)->bool)->bool)->(((num#O#M)->bool)->bool).
                    is_linear ring_carrier
                      (module_carrier x) (module_zero x)
                      (module_add x) (module_smul x)
                      (module_carrier y) (module_zero y)
                      (module_add y) (module_smul y) linear
                    ==> ?f:M.
                          hom objects morphisms dom cod x y f /\
                          !u:((num#O#M)->bool)->bool.
                            module_carrier x u
                            ==> functor_morphism f u = linear u) /\
           (!x y:O. !f g:M.
              hom objects morphisms dom cod x y f /\
              hom objects morphisms dom cod x y g /\
              (!u:((num#O#M)->bool)->bool.
                 module_carrier x u
                 ==> functor_morphism f u = functor_morphism g u)
              ==> f = g) /\
           (!z:O.
              is_zero_object objects morphisms dom cod z
              ==> !u:((num#O#M)->bool)->bool.
                    module_carrier z u ==> u = module_zero z) /\
           (!x y p:O. !i1 i2 p1 p2:M.
              is_biproduct objects morphisms dom cod identity compose
                zero add x y p i1 i2 p1 p2
              ==> !u:((num#O#M)->bool)->bool.
                    !v:((num#O#M)->bool)->bool.
                      module_carrier x u /\ module_carrier y v
                      ==> ?w:((num#O#M)->bool)->bool.
                            module_carrier p w /\
                            functor_morphism p1 w = u /\
                            functor_morphism p2 w = v /\
                            !w':((num#O#M)->bool)->bool.
                              module_carrier p w' /\
                              functor_morphism p1 w' = u /\
                              functor_morphism p2 w' = v
                              ==> w' = w) /\
           (!kobject a b:O. !k f:M.
              is_kernel objects morphisms dom cod compose zero
                kobject a b k f
              ==> (!u v:((num#O#M)->bool)->bool.
                     module_carrier kobject u /\
                     module_carrier kobject v /\
                     functor_morphism k u = functor_morphism k v
                     ==> u = v) /\
                  (!v:((num#O#M)->bool)->bool.
                     module_carrier a v
                     ==> (functor_morphism f v = module_zero b <=>
                          ?u:((num#O#M)->bool)->bool.
                            module_carrier kobject u /\
                            functor_morphism k u = v))) /\
           (!a b qobject:O. !f q:M.
              is_cokernel objects morphisms dom cod compose zero
                a b qobject f q
              ==> (!w:((num#O#M)->bool)->bool.
                     module_carrier qobject w
                     ==> ?v:((num#O#M)->bool)->bool.
                           module_carrier b v /\
                           functor_morphism q v = w) /\
                  (!v:((num#O#M)->bool)->bool.
                     module_carrier b v
                     ==> (functor_morphism q v = module_zero qobject <=>
                          ?u:((num#O#M)->bool)->bool.
                            module_carrier a u /\
                            functor_morphism f u = v)))`;;
