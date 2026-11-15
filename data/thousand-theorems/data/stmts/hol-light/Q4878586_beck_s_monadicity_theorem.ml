(*
  Statement-only formalization of Thousand Theorems corpus artifact Q4878586,
  "Beck's monadicity theorem": a right adjoint that creates coequalizers of
  the pairs split by that functor is monadic. This file contains no proof.
*)

let Q4878586_BECK_S_MONADICITY_THEOREM =
  `let Chom =
     \(Cobjects:CO->bool) (Cmorphisms:CM->bool)
      (Cdom:CM->CO) (Ccod:CM->CO) (x:CO) (y:CO) (f:CM).
       Cobjects x /\ Cobjects y /\ Cmorphisms f /\
       Cdom f = x /\ Ccod f = y in
   let Dhom =
     \(Dobjects:DO->bool) (Dmorphisms:DM->bool)
      (Ddom:DM->DO) (Dcod:DM->DO) (x:DO) (y:DO) (f:DM).
       Dobjects x /\ Dobjects y /\ Dmorphisms f /\
       Ddom f = x /\ Dcod f = y in
   let is_C_category =
     \(Cobjects:CO->bool) (Cmorphisms:CM->bool)
      (Cdom:CM->CO) (Ccod:CM->CO)
      (Cidentity:CO->CM) (Ccompose:CM->CM->CM).
       (!f:CM.
          Cmorphisms f ==> Cobjects (Cdom f) /\ Cobjects (Ccod f)) /\
       (!x:CO.
          Cobjects x
          ==> Chom Cobjects Cmorphisms Cdom Ccod
                x x (Cidentity x)) /\
       (!x y z:CO. !f g:CM.
          Chom Cobjects Cmorphisms Cdom Ccod x y f /\
          Chom Cobjects Cmorphisms Cdom Ccod y z g
          ==> Chom Cobjects Cmorphisms Cdom Ccod
                x z (Ccompose g f)) /\
       (!x y:CO. !f:CM.
          Chom Cobjects Cmorphisms Cdom Ccod x y f
          ==> Ccompose (Cidentity y) f = f /\
              Ccompose f (Cidentity x) = f) /\
       (!w x y z:CO. !f g h:CM.
          Chom Cobjects Cmorphisms Cdom Ccod w x f /\
          Chom Cobjects Cmorphisms Cdom Ccod x y g /\
          Chom Cobjects Cmorphisms Cdom Ccod y z h
          ==> Ccompose h (Ccompose g f) =
              Ccompose (Ccompose h g) f) in
   let is_D_category =
     \(Dobjects:DO->bool) (Dmorphisms:DM->bool)
      (Ddom:DM->DO) (Dcod:DM->DO)
      (Didentity:DO->DM) (Dcompose:DM->DM->DM).
       (!f:DM.
          Dmorphisms f ==> Dobjects (Ddom f) /\ Dobjects (Dcod f)) /\
       (!x:DO.
          Dobjects x
          ==> Dhom Dobjects Dmorphisms Ddom Dcod
                x x (Didentity x)) /\
       (!x y z:DO. !f g:DM.
          Dhom Dobjects Dmorphisms Ddom Dcod x y f /\
          Dhom Dobjects Dmorphisms Ddom Dcod y z g
          ==> Dhom Dobjects Dmorphisms Ddom Dcod
                x z (Dcompose g f)) /\
       (!x y:DO. !f:DM.
          Dhom Dobjects Dmorphisms Ddom Dcod x y f
          ==> Dcompose (Didentity y) f = f /\
              Dcompose f (Didentity x) = f) /\
       (!w x y z:DO. !f g h:DM.
          Dhom Dobjects Dmorphisms Ddom Dcod w x f /\
          Dhom Dobjects Dmorphisms Ddom Dcod x y g /\
          Dhom Dobjects Dmorphisms Ddom Dcod y z h
          ==> Dcompose h (Dcompose g f) =
              Dcompose (Dcompose h g) f) in
   let is_functor_F =
     \(Cobjects:CO->bool) (Cmorphisms:CM->bool)
      (Cdom:CM->CO) (Ccod:CM->CO)
      (Cidentity:CO->CM) (Ccompose:CM->CM->CM)
      (Dobjects:DO->bool) (Dmorphisms:DM->bool)
      (Ddom:DM->DO) (Dcod:DM->DO)
      (Didentity:DO->DM) (Dcompose:DM->DM->DM)
      (Fobject:CO->DO) (Fmorphism:CM->DM).
       (!x:CO. Cobjects x ==> Dobjects (Fobject x)) /\
       (!x y:CO. !f:CM.
          Chom Cobjects Cmorphisms Cdom Ccod x y f
          ==> Dhom Dobjects Dmorphisms Ddom Dcod
                (Fobject x) (Fobject y) (Fmorphism f)) /\
       (!x:CO.
          Cobjects x
          ==> Fmorphism (Cidentity x) = Didentity (Fobject x)) /\
       (!x y z:CO. !f g:CM.
          Chom Cobjects Cmorphisms Cdom Ccod x y f /\
          Chom Cobjects Cmorphisms Cdom Ccod y z g
          ==> Fmorphism (Ccompose g f) =
              Dcompose (Fmorphism g) (Fmorphism f)) in
   let is_functor_G =
     \(Cobjects:CO->bool) (Cmorphisms:CM->bool)
      (Cdom:CM->CO) (Ccod:CM->CO)
      (Cidentity:CO->CM) (Ccompose:CM->CM->CM)
      (Dobjects:DO->bool) (Dmorphisms:DM->bool)
      (Ddom:DM->DO) (Dcod:DM->DO)
      (Didentity:DO->DM) (Dcompose:DM->DM->DM)
      (Gobject:DO->CO) (Gmorphism:DM->CM).
       (!x:DO. Dobjects x ==> Cobjects (Gobject x)) /\
       (!x y:DO. !f:DM.
          Dhom Dobjects Dmorphisms Ddom Dcod x y f
          ==> Chom Cobjects Cmorphisms Cdom Ccod
                (Gobject x) (Gobject y) (Gmorphism f)) /\
       (!x:DO.
          Dobjects x
          ==> Gmorphism (Didentity x) = Cidentity (Gobject x)) /\
       (!x y z:DO. !f g:DM.
          Dhom Dobjects Dmorphisms Ddom Dcod x y f /\
          Dhom Dobjects Dmorphisms Ddom Dcod y z g
          ==> Gmorphism (Dcompose g f) =
              Ccompose (Gmorphism g) (Gmorphism f)) in
   let is_adjunction =
     \(Cobjects:CO->bool) (Cmorphisms:CM->bool)
      (Cdom:CM->CO) (Ccod:CM->CO)
      (Cidentity:CO->CM) (Ccompose:CM->CM->CM)
      (Dobjects:DO->bool) (Dmorphisms:DM->bool)
      (Ddom:DM->DO) (Dcod:DM->DO)
      (Didentity:DO->DM) (Dcompose:DM->DM->DM)
      (Fobject:CO->DO) (Fmorphism:CM->DM)
      (Gobject:DO->CO) (Gmorphism:DM->CM)
      (unit:CO->CM) (counit:DO->DM).
       (!x:CO.
          Cobjects x
          ==> Chom Cobjects Cmorphisms Cdom Ccod
                x (Gobject (Fobject x)) (unit x)) /\
       (!y:DO.
          Dobjects y
          ==> Dhom Dobjects Dmorphisms Ddom Dcod
                (Fobject (Gobject y)) y (counit y)) /\
       (!x x':CO. !f:CM.
          Chom Cobjects Cmorphisms Cdom Ccod x x' f
          ==> Ccompose
                (Gmorphism (Fmorphism f)) (unit x) =
              Ccompose (unit x') f) /\
       (!y y':DO. !g:DM.
          Dhom Dobjects Dmorphisms Ddom Dcod y y' g
          ==> Dcompose g (counit y) =
              Dcompose (counit y')
                (Fmorphism (Gmorphism g))) /\
       (!x:CO.
          Cobjects x
          ==> Dcompose (counit (Fobject x))
                (Fmorphism (unit x)) =
              Didentity (Fobject x)) /\
       (!y:DO.
          Dobjects y
          ==> Ccompose (Gmorphism (counit y))
                (unit (Gobject y)) =
              Cidentity (Gobject y)) in
   let is_C_coequalizer =
     \(Cobjects:CO->bool) (Cmorphisms:CM->bool)
      (Cdom:CM->CO) (Ccod:CM->CO)
      (Ccompose:CM->CM->CM)
      (x:CO) (y:CO) (f:CM) (g:CM) (z:CO) (q:CM).
       Chom Cobjects Cmorphisms Cdom Ccod x y f /\
       Chom Cobjects Cmorphisms Cdom Ccod x y g /\
       Chom Cobjects Cmorphisms Cdom Ccod y z q /\
       Ccompose q f = Ccompose q g /\
       (!w:CO. !h:CM.
          Chom Cobjects Cmorphisms Cdom Ccod y w h /\
          Ccompose h f = Ccompose h g
          ==> ?u:CM.
                Chom Cobjects Cmorphisms Cdom Ccod z w u /\
                Ccompose u q = h /\
                !v:CM.
                  Chom Cobjects Cmorphisms Cdom Ccod z w v /\
                  Ccompose v q = h
                  ==> v = u) in
   let is_D_coequalizer =
     \(Dobjects:DO->bool) (Dmorphisms:DM->bool)
      (Ddom:DM->DO) (Dcod:DM->DO)
      (Dcompose:DM->DM->DM)
      (x:DO) (y:DO) (f:DM) (g:DM) (z:DO) (q:DM).
       Dhom Dobjects Dmorphisms Ddom Dcod x y f /\
       Dhom Dobjects Dmorphisms Ddom Dcod x y g /\
       Dhom Dobjects Dmorphisms Ddom Dcod y z q /\
       Dcompose q f = Dcompose q g /\
       (!w:DO. !h:DM.
          Dhom Dobjects Dmorphisms Ddom Dcod y w h /\
          Dcompose h f = Dcompose h g
          ==> ?u:DM.
                Dhom Dobjects Dmorphisms Ddom Dcod z w u /\
                Dcompose u q = h /\
                !v:DM.
                  Dhom Dobjects Dmorphisms Ddom Dcod z w v /\
                  Dcompose v q = h
                  ==> v = u) in
   let is_G_split_pair =
     \(Cobjects:CO->bool) (Cmorphisms:CM->bool)
      (Cdom:CM->CO) (Ccod:CM->CO)
      (Cidentity:CO->CM) (Ccompose:CM->CM->CM)
      (Dobjects:DO->bool) (Dmorphisms:DM->bool)
      (Ddom:DM->DO) (Dcod:DM->DO)
      (Gobject:DO->CO) (Gmorphism:DM->CM)
      (x:DO) (y:DO) (f:DM) (g:DM).
       Dhom Dobjects Dmorphisms Ddom Dcod x y f /\
       Dhom Dobjects Dmorphisms Ddom Dcod x y g /\
       ?z:CO. ?q section retract:CM.
         Chom Cobjects Cmorphisms Cdom Ccod
           (Gobject y) z q /\
         Chom Cobjects Cmorphisms Cdom Ccod
           z (Gobject y) section /\
         Chom Cobjects Cmorphisms Cdom Ccod
           (Gobject y) (Gobject x) retract /\
         Ccompose q (Gmorphism f) =
           Ccompose q (Gmorphism g) /\
         Ccompose q section = Cidentity z /\
         Ccompose (Gmorphism g) retract =
           Cidentity (Gobject y) /\
         Ccompose (Gmorphism f) retract =
           Ccompose section q in
   let creates_G_split_coequalizers =
     \(Cobjects:CO->bool) (Cmorphisms:CM->bool)
      (Cdom:CM->CO) (Ccod:CM->CO)
      (Cidentity:CO->CM) (Ccompose:CM->CM->CM)
      (Dobjects:DO->bool) (Dmorphisms:DM->bool)
      (Ddom:DM->DO) (Dcod:DM->DO)
      (Dcompose:DM->DM->DM)
      (Gobject:DO->CO) (Gmorphism:DM->CM).
       !x y:DO. !f g:DM.
         is_G_split_pair
           Cobjects Cmorphisms Cdom Ccod Cidentity Ccompose
           Dobjects Dmorphisms Ddom Dcod
           Gobject Gmorphism x y f g
         ==> ((!w:DO. !r:DM.
                 Dhom Dobjects Dmorphisms Ddom Dcod y w r /\
                 Dcompose r f = Dcompose r g /\
                 is_C_coequalizer
                   Cobjects Cmorphisms Cdom Ccod Ccompose
                   (Gobject x) (Gobject y)
                   (Gmorphism f) (Gmorphism g)
                   (Gobject w) (Gmorphism r)
                 ==> is_D_coequalizer
                       Dobjects Dmorphisms Ddom Dcod Dcompose
                       x y f g w r) /\
              (!z:CO. !q:CM.
                 is_C_coequalizer
                   Cobjects Cmorphisms Cdom Ccod Ccompose
                   (Gobject x) (Gobject y)
                   (Gmorphism f) (Gmorphism g) z q
                 ==> ?w:DO. ?r:DM. ?i j:CM.
                       Dobjects w /\
                       Dhom Dobjects Dmorphisms Ddom Dcod y w r /\
                       Dcompose r f = Dcompose r g /\
                       Chom Cobjects Cmorphisms Cdom Ccod
                         (Gobject w) z i /\
                       Chom Cobjects Cmorphisms Cdom Ccod
                         z (Gobject w) j /\
                       Ccompose j i = Cidentity (Gobject w) /\
                       Ccompose i j = Cidentity z /\
                       Ccompose i (Gmorphism r) = q)) in
   let is_algebra =
     \(Cobjects:CO->bool) (Cmorphisms:CM->bool)
      (Cdom:CM->CO) (Ccod:CM->CO)
      (Cidentity:CO->CM) (Ccompose:CM->CM->CM)
      (Fobject:CO->DO) (Fmorphism:CM->DM)
      (Gobject:DO->CO) (Gmorphism:DM->CM)
      (unit:CO->CM) (counit:DO->DM)
      (x:CO) (action:CM).
       Cobjects x /\
       Chom Cobjects Cmorphisms Cdom Ccod
         (Gobject (Fobject x)) x action /\
       Ccompose action (unit x) = Cidentity x /\
       Ccompose action (Gmorphism (Fmorphism action)) =
         Ccompose action (Gmorphism (counit (Fobject x))) in
   let is_algebra_morphism =
     \(Cobjects:CO->bool) (Cmorphisms:CM->bool)
      (Cdom:CM->CO) (Ccod:CM->CO)
      (Ccompose:CM->CM->CM)
      (Fmorphism:CM->DM) (Gmorphism:DM->CM)
      (x:CO) (action_x:CM) (y:CO) (action_y:CM) (h:CM).
       Chom Cobjects Cmorphisms Cdom Ccod x y h /\
       Ccompose h action_x =
         Ccompose action_y (Gmorphism (Fmorphism h)) in
   let is_monadic_for_adjunction =
     \(Cobjects:CO->bool) (Cmorphisms:CM->bool)
      (Cdom:CM->CO) (Ccod:CM->CO)
      (Cidentity:CO->CM) (Ccompose:CM->CM->CM)
      (Dobjects:DO->bool) (Dmorphisms:DM->bool)
      (Ddom:DM->DO) (Dcod:DM->DO)
      (Fobject:CO->DO) (Fmorphism:CM->DM)
      (Gobject:DO->CO) (Gmorphism:DM->CM)
      (unit:CO->CM) (counit:DO->DM).
       (!x y:DO.
          Dobjects x /\ Dobjects y
          ==> (!f:DM.
                 Dhom Dobjects Dmorphisms Ddom Dcod x y f
                 ==> is_algebra_morphism
                       Cobjects Cmorphisms Cdom Ccod Ccompose
                       Fmorphism Gmorphism
                       (Gobject x) (Gmorphism (counit x))
                       (Gobject y) (Gmorphism (counit y))
                       (Gmorphism f)) /\
              (!h:CM.
                 is_algebra_morphism
                   Cobjects Cmorphisms Cdom Ccod Ccompose
                   Fmorphism Gmorphism
                   (Gobject x) (Gmorphism (counit x))
                   (Gobject y) (Gmorphism (counit y)) h
                 ==> ?f:DM.
                       Dhom Dobjects Dmorphisms Ddom Dcod x y f /\
                       Gmorphism f = h /\
                       !g:DM.
                         Dhom Dobjects Dmorphisms Ddom Dcod x y g /\
                         Gmorphism g = h
                         ==> g = f)) /\
       (!x:CO. !action:CM.
          is_algebra
            Cobjects Cmorphisms Cdom Ccod Cidentity Ccompose
            Fobject Fmorphism Gobject Gmorphism unit counit
            x action
          ==> ?y:DO. ?p q:CM.
                Dobjects y /\
                is_algebra_morphism
                  Cobjects Cmorphisms Cdom Ccod Ccompose
                  Fmorphism Gmorphism
                  x action
                  (Gobject y) (Gmorphism (counit y)) p /\
                is_algebra_morphism
                  Cobjects Cmorphisms Cdom Ccod Ccompose
                  Fmorphism Gmorphism
                  (Gobject y) (Gmorphism (counit y))
                  x action q /\
                Ccompose q p = Cidentity x /\
                Ccompose p q = Cidentity (Gobject y)) in
   let is_monadic_right_adjoint =
     \(Cobjects:CO->bool) (Cmorphisms:CM->bool)
      (Cdom:CM->CO) (Ccod:CM->CO)
      (Cidentity:CO->CM) (Ccompose:CM->CM->CM)
      (Dobjects:DO->bool) (Dmorphisms:DM->bool)
      (Ddom:DM->DO) (Dcod:DM->DO)
      (Didentity:DO->DM) (Dcompose:DM->DM->DM)
      (Gobject:DO->CO) (Gmorphism:DM->CM).
       ?Fobject:CO->DO. ?Fmorphism:CM->DM.
       ?unit:CO->CM. ?counit:DO->DM.
         is_functor_F
           Cobjects Cmorphisms Cdom Ccod Cidentity Ccompose
           Dobjects Dmorphisms Ddom Dcod Didentity Dcompose
           Fobject Fmorphism /\
         is_adjunction
           Cobjects Cmorphisms Cdom Ccod Cidentity Ccompose
           Dobjects Dmorphisms Ddom Dcod Didentity Dcompose
           Fobject Fmorphism Gobject Gmorphism unit counit /\
         is_monadic_for_adjunction
           Cobjects Cmorphisms Cdom Ccod Cidentity Ccompose
           Dobjects Dmorphisms Ddom Dcod
           Fobject Fmorphism Gobject Gmorphism unit counit in
   !Cobjects:CO->bool. !Cmorphisms:CM->bool.
   !Cdom:CM->CO. !Ccod:CM->CO.
   !Cidentity:CO->CM. !Ccompose:CM->CM->CM.
   !Dobjects:DO->bool. !Dmorphisms:DM->bool.
   !Ddom:DM->DO. !Dcod:DM->DO.
   !Didentity:DO->DM. !Dcompose:DM->DM->DM.
   !Fobject:CO->DO. !Fmorphism:CM->DM.
   !Gobject:DO->CO. !Gmorphism:DM->CM.
   !unit:CO->CM. !counit:DO->DM.
     is_C_category
       Cobjects Cmorphisms Cdom Ccod Cidentity Ccompose /\
     is_D_category
       Dobjects Dmorphisms Ddom Dcod Didentity Dcompose /\
     is_functor_F
       Cobjects Cmorphisms Cdom Ccod Cidentity Ccompose
       Dobjects Dmorphisms Ddom Dcod Didentity Dcompose
       Fobject Fmorphism /\
     is_functor_G
       Cobjects Cmorphisms Cdom Ccod Cidentity Ccompose
       Dobjects Dmorphisms Ddom Dcod Didentity Dcompose
       Gobject Gmorphism /\
     is_adjunction
       Cobjects Cmorphisms Cdom Ccod Cidentity Ccompose
       Dobjects Dmorphisms Ddom Dcod Didentity Dcompose
       Fobject Fmorphism Gobject Gmorphism unit counit /\
     creates_G_split_coequalizers
       Cobjects Cmorphisms Cdom Ccod Cidentity Ccompose
       Dobjects Dmorphisms Ddom Dcod Dcompose
       Gobject Gmorphism
     ==> is_monadic_right_adjoint
           Cobjects Cmorphisms Cdom Ccod Cidentity Ccompose
           Dobjects Dmorphisms Ddom Dcod Didentity Dcompose
           Gobject Gmorphism`;;
