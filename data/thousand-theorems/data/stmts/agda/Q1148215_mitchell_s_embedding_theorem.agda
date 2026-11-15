-- Statement-only formalization of thousand-theorems corpus artifact Q1148215,
-- "Mitchell's embedding theorem": every abelian category admits a full,
-- faithful, finite-limit- and finite-colimit-preserving functor into a
-- category of modules over a ring. This file contains no proof.

{-# OPTIONS --safe #-}

module Q1148215_mitchell_s_embedding_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_; Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Sigma using (Σ)

infixr 2 _×_

record _×_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

PointwiseEqual :
  {a b : Level} →
  {A : Set a} →
  {B : Set b} →
  (A → B) →
  (A → B) →
  Set (a ⊔ b)
PointwiseEqual {A = A} f g =
  (x : A) → f x ≡ g x

data Member
  {a : Level}
  {A : Set a}
  (x : A) :
  List A →
  Set a where

  at-head :
    {xs : List A} →
    Member x (x ∷ xs)

  in-tail :
    {y : A} →
    {xs : List A} →
    Member x xs →
    Member x (y ∷ xs)

record Finite
  {a : Level}
  (A : Set a) :
  Set a where

  field
    enumeration : List A
    exhaustive  : (x : A) → Member x enumeration

record AbelianGroup
  {a : Level}
  (A : Set a) :
  Set a where

  field
    zero            : A
    add             : A → A → A
    negate          : A → A
    add-associative :
      (x y z : A) →
      add (add x y) z ≡ add x (add y z)
    add-commutative :
      (x y : A) →
      add x y ≡ add y x
    add-zero :
      (x : A) →
      add x zero ≡ x
    add-inverse :
      (x : A) →
      add x (negate x) ≡ zero

record Ring
  {r : Level}
  (R : Set r) :
  Set r where

  field
    additive-group : AbelianGroup R
    one             : R
    multiply        : R → R → R
    multiply-associative :
      (x y z : R) →
      multiply (multiply x y) z ≡
      multiply x (multiply y z)
    multiply-one-left :
      (x : R) →
      multiply one x ≡ x
    multiply-one-right :
      (x : R) →
      multiply x one ≡ x
    distribute-left :
      (x y z : R) →
      multiply x (AbelianGroup.add additive-group y z) ≡
      AbelianGroup.add additive-group
        (multiply x y)
        (multiply x z)
    distribute-right :
      (x y z : R) →
      multiply (AbelianGroup.add additive-group x y) z ≡
      AbelianGroup.add additive-group
        (multiply x z)
        (multiply y z)

record LeftModule
  {r m : Level}
  {R : Set r}
  (ring : Ring R)
  (M : Set m) :
  Set (r ⊔ m) where

  field
    additive-group : AbelianGroup M
    scale          : R → M → M
    scale-add :
      (a : R) (x y : M) →
      scale a (AbelianGroup.add additive-group x y) ≡
      AbelianGroup.add additive-group (scale a x) (scale a y)
    add-scale :
      (a b : R) (x : M) →
      scale
        (AbelianGroup.add (Ring.additive-group ring) a b)
        x
      ≡
      AbelianGroup.add additive-group (scale a x) (scale b x)
    multiply-scale :
      (a b : R) (x : M) →
      scale (Ring.multiply ring a b) x ≡ scale a (scale b x)
    one-scale :
      (x : M) →
      scale (Ring.one ring) x ≡ x

record ModuleObject
  {r : Level}
  {R : Set r}
  (ring : Ring R)
  (m : Level) :
  Set (r ⊔ lsuc m) where

  field
    Carrier          : Set m
    module-structure : LeftModule ring Carrier

record IsLinear
  {r m : Level}
  {R : Set r}
  {ring : Ring R}
  (M N : ModuleObject ring m)
  (function :
    ModuleObject.Carrier M →
    ModuleObject.Carrier N) :
  Set (r ⊔ m) where

  private
    module M = LeftModule (ModuleObject.module-structure M)
    module N = LeftModule (ModuleObject.module-structure N)

  field
    map-add :
      (x y : ModuleObject.Carrier M) →
      function (AbelianGroup.add M.additive-group x y) ≡
      AbelianGroup.add N.additive-group (function x) (function y)
    map-scale :
      (a : R) (x : ModuleObject.Carrier M) →
      function (M.scale a x) ≡ N.scale a (function x)

record Category
  {o h : Level}
  (Object : Set o) :
  Set (o ⊔ lsuc h) where

  infixr 7 _after_

  field
    Hom      : Object → Object → Set h
    identity : (A : Object) → Hom A A
    _after_  :
      {A B C : Object} →
      Hom B C →
      Hom A B →
      Hom A C
    compose-associative :
      {A B C D : Object} →
      (h : Hom C D) →
      (g : Hom B C) →
      (f : Hom A B) →
      h after (g after f) ≡ (h after g) after f
    identity-left :
      {A B : Object} →
      (f : Hom A B) →
      identity B after f ≡ f
    identity-right :
      {A B : Object} →
      (f : Hom A B) →
      f after identity A ≡ f

record Preadditive
  {o h : Level}
  {Object : Set o}
  (category : Category {o} {h} Object) :
  Set (o ⊔ h) where

  private
    module C = Category category

  field
    hom-additive-group :
      (A B : Object) →
      AbelianGroup (C.Hom A B)
    compose-add-left :
      {A B C : Object} →
      (f g : C.Hom B C) →
      (h : C.Hom A B) →
      C._after_
        (AbelianGroup.add (hom-additive-group B C) f g)
        h
      ≡
      AbelianGroup.add
        (hom-additive-group A C)
        (C._after_ f h)
        (C._after_ g h)
    compose-add-right :
      {A B C : Object} →
      (f : C.Hom B C) →
      (g h : C.Hom A B) →
      C._after_
        f
        (AbelianGroup.add (hom-additive-group A B) g h)
      ≡
      AbelianGroup.add
        (hom-additive-group A C)
        (C._after_ f g)
        (C._after_ f h)

ZeroMorphism :
  {o h : Level} →
  {Object : Set o} →
  {category : Category {o} {h} Object} →
  Preadditive category →
  (A B : Object) →
  Category.Hom category A B
ZeroMorphism preadditive A B =
  AbelianGroup.zero
    (Preadditive.hom-additive-group preadditive A B)

record ZeroObject
  {o h : Level}
  {Object : Set o}
  (category : Category {o} {h} Object) :
  Set (o ⊔ h) where

  private
    module C = Category category

  field
    object : Object
    from   : (A : Object) → C.Hom object A
    to     : (A : Object) → C.Hom A object
    from-unique :
      (A : Object) →
      (f : C.Hom object A) →
      f ≡ from A
    to-unique :
      (A : Object) →
      (f : C.Hom A object) →
      f ≡ to A

record BinaryProduct
  {o h : Level}
  {Object : Set o}
  (category : Category {o} {h} Object)
  (A B : Object) :
  Set (o ⊔ h) where

  private
    module C = Category category

  field
    object     : Object
    projection-left  : C.Hom object A
    projection-right : C.Hom object B
    universal :
      (X : Object) →
      (f : C.Hom X A) →
      (g : C.Hom X B) →
      Σ (C.Hom X object)
        (λ lift →
          (C._after_ projection-left lift ≡ f)
          ×
          ((C._after_ projection-right lift ≡ g)
          ×
          ((other : C.Hom X object) →
            C._after_ projection-left other ≡ f →
            C._after_ projection-right other ≡ g →
            other ≡ lift)))

record BinaryCoproduct
  {o h : Level}
  {Object : Set o}
  (category : Category {o} {h} Object)
  (A B : Object) :
  Set (o ⊔ h) where

  private
    module C = Category category

  field
    object    : Object
    injection-left  : C.Hom A object
    injection-right : C.Hom B object
    universal :
      (X : Object) →
      (f : C.Hom A X) →
      (g : C.Hom B X) →
      Σ (C.Hom object X)
        (λ descend →
          (C._after_ descend injection-left ≡ f)
          ×
          ((C._after_ descend injection-right ≡ g)
          ×
          ((other : C.Hom object X) →
            C._after_ other injection-left ≡ f →
            C._after_ other injection-right ≡ g →
            other ≡ descend)))

record IsKernel
  {o h : Level}
  {Object : Set o}
  {category : Category {o} {h} Object}
  (preadditive : Preadditive category)
  {K A B : Object}
  (kernel-arrow : Category.Hom category K A)
  (arrow : Category.Hom category A B) :
  Set (o ⊔ h) where

  private
    module C = Category category

  field
    annihilates :
      C._after_ arrow kernel-arrow ≡
      ZeroMorphism preadditive K B
    universal :
      (X : Object) →
      (f : C.Hom X A) →
      C._after_ arrow f ≡ ZeroMorphism preadditive X B →
      Σ (C.Hom X K)
        (λ lift →
          (C._after_ kernel-arrow lift ≡ f)
          ×
          ((other : C.Hom X K) →
            C._after_ kernel-arrow other ≡ f →
            other ≡ lift))

record IsCokernel
  {o h : Level}
  {Object : Set o}
  {category : Category {o} {h} Object}
  (preadditive : Preadditive category)
  {A B Q : Object}
  (arrow : Category.Hom category A B)
  (cokernel-arrow : Category.Hom category B Q) :
  Set (o ⊔ h) where

  private
    module C = Category category

  field
    annihilates :
      C._after_ cokernel-arrow arrow ≡
      ZeroMorphism preadditive A Q
    universal :
      (X : Object) →
      (f : C.Hom B X) →
      C._after_ f arrow ≡ ZeroMorphism preadditive A X →
      Σ (C.Hom Q X)
        (λ descend →
          (C._after_ descend cokernel-arrow ≡ f)
          ×
          ((other : C.Hom Q X) →
            C._after_ other cokernel-arrow ≡ f →
            other ≡ descend))

Monomorphism :
  {o h : Level} →
  {Object : Set o} →
  (category : Category {o} {h} Object) →
  {A B : Object} →
  Category.Hom category A B →
  Set (o ⊔ h)
Monomorphism {Object = Object} category {A} arrow =
  (X : Object) →
  (f g : Category.Hom category X A) →
  Category._after_ category arrow f ≡
  Category._after_ category arrow g →
  f ≡ g

Epimorphism :
  {o h : Level} →
  {Object : Set o} →
  (category : Category {o} {h} Object) →
  {A B : Object} →
  Category.Hom category A B →
  Set (o ⊔ h)
Epimorphism {Object = Object} category {B = B} arrow =
  (X : Object) →
  (f g : Category.Hom category B X) →
  Category._after_ category f arrow ≡
  Category._after_ category g arrow →
  f ≡ g

record AbelianCategory
  {o h : Level}
  {Object : Set o}
  (category : Category {o} {h} Object) :
  Set (lsuc (o ⊔ h)) where

  private
    module C = Category category

  field
    preadditive : Preadditive category
    zero-object : ZeroObject category
    binary-products :
      (A B : Object) →
      BinaryProduct category A B
    binary-coproducts :
      (A B : Object) →
      BinaryCoproduct category A B
    kernels :
      {A B : Object} →
      (f : C.Hom A B) →
      Σ Object
        (λ K →
          Σ (C.Hom K A)
            (λ kernel-arrow →
              IsKernel preadditive kernel-arrow f))
    cokernels :
      {A B : Object} →
      (f : C.Hom A B) →
      Σ Object
        (λ Q →
          Σ (C.Hom B Q)
            (λ cokernel-arrow →
              IsCokernel preadditive f cokernel-arrow))
    every-monomorphism-is-normal :
      {A B : Object} →
      (f : C.Hom A B) →
      Monomorphism category f →
      Σ Object
        (λ Q →
          Σ (C.Hom B Q)
            (λ g → IsKernel preadditive f g))
    every-epimorphism-is-normal :
      {A B : Object} →
      (f : C.Hom A B) →
      Epimorphism category f →
      Σ Object
        (λ K →
          Σ (C.Hom K A)
            (λ g → IsCokernel preadditive g f))

record Diagram
  {jo jh o h : Level}
  {Index : Set jo}
  {Object : Set o}
  (index-category : Category {jo} {jh} Index)
  (category : Category {o} {h} Object) :
  Set (jo ⊔ jh ⊔ o ⊔ h) where

  private
    module J = Category index-category
    module C = Category category

  field
    object-map : Index → Object
    arrow-map :
      {i j : Index} →
      J.Hom i j →
      C.Hom (object-map i) (object-map j)
    map-identity :
      (i : Index) →
      arrow-map (J.identity i) ≡ C.identity (object-map i)
    map-compose :
      {i j k : Index} →
      (g : J.Hom j k) →
      (f : J.Hom i j) →
      arrow-map (J._after_ g f) ≡
      C._after_ (arrow-map g) (arrow-map f)

record FiniteCategory
  {o h : Level}
  {Object : Set o}
  (category : Category {o} {h} Object) :
  Set (o ⊔ h) where

  field
    finite-objects : Finite Object
    finite-arrows :
      (A B : Object) →
      Finite (Category.Hom category A B)

record Cone
  {jo jh o h : Level}
  {Index : Set jo}
  {Object : Set o}
  {index-category : Category {jo} {jh} Index}
  {category : Category {o} {h} Object}
  (diagram : Diagram index-category category)
  (apex : Object) :
  Set (jo ⊔ jh ⊔ o ⊔ h) where

  private
    module J = Category index-category
    module C = Category category
    module D = Diagram diagram

  field
    leg :
      (i : Index) →
      C.Hom apex (D.object-map i)
    natural :
      {i j : Index} →
      (f : J.Hom i j) →
      C._after_ (D.arrow-map f) (leg i) ≡ leg j

record IsLimit
  {jo jh o h : Level}
  {Index : Set jo}
  {Object : Set o}
  {index-category : Category {jo} {jh} Index}
  {category : Category {o} {h} Object}
  {diagram : Diagram index-category category}
  {apex : Object}
  (cone : Cone diagram apex) :
  Set (jo ⊔ jh ⊔ o ⊔ h) where

  private
    module C = Category category

  field
    universal :
      (X : Object) →
      (other : Cone diagram X) →
      Σ (C.Hom X apex)
        (λ factor →
          ((i : Index) →
            C._after_ (Cone.leg cone i) factor ≡
            Cone.leg other i)
          ×
          ((candidate : C.Hom X apex) →
            ((i : Index) →
              C._after_ (Cone.leg cone i) candidate ≡
              Cone.leg other i) →
            candidate ≡ factor))

record Cocone
  {jo jh o h : Level}
  {Index : Set jo}
  {Object : Set o}
  {index-category : Category {jo} {jh} Index}
  {category : Category {o} {h} Object}
  (diagram : Diagram index-category category)
  (apex : Object) :
  Set (jo ⊔ jh ⊔ o ⊔ h) where

  private
    module J = Category index-category
    module C = Category category
    module D = Diagram diagram

  field
    leg :
      (i : Index) →
      C.Hom (D.object-map i) apex
    natural :
      {i j : Index} →
      (f : J.Hom i j) →
      C._after_ (leg j) (D.arrow-map f) ≡ leg i

record IsColimit
  {jo jh o h : Level}
  {Index : Set jo}
  {Object : Set o}
  {index-category : Category {jo} {jh} Index}
  {category : Category {o} {h} Object}
  {diagram : Diagram index-category category}
  {apex : Object}
  (cocone : Cocone diagram apex) :
  Set (jo ⊔ jh ⊔ o ⊔ h) where

  private
    module C = Category category

  field
    universal :
      (X : Object) →
      (other : Cocone diagram X) →
      Σ (C.Hom apex X)
        (λ factor →
          ((i : Index) →
            C._after_ factor (Cocone.leg cocone i) ≡
            Cocone.leg other i)
          ×
          ((candidate : C.Hom apex X) →
            ((i : Index) →
              C._after_ candidate (Cocone.leg cocone i) ≡
              Cocone.leg other i) →
            candidate ≡ factor))

record FunctorToModules
  {o h r m : Level}
  {Object : Set o}
  {R : Set r}
  (category : Category {o} {h} Object)
  (ring : Ring R) :
  Set (o ⊔ h ⊔ r ⊔ lsuc m) where

  private
    module C = Category category

  field
    object-map :
      Object →
      ModuleObject ring m
    arrow-map :
      {A B : Object} →
      C.Hom A B →
      ModuleObject.Carrier (object-map A) →
      ModuleObject.Carrier (object-map B)
    arrow-linear :
      {A B : Object} →
      (f : C.Hom A B) →
      IsLinear (object-map A) (object-map B) (arrow-map f)
    map-identity :
      (A : Object) →
      PointwiseEqual
        (arrow-map (C.identity A))
        (λ x → x)
    map-compose :
      {A B D : Object} →
      (g : C.Hom B D) →
      (f : C.Hom A B) →
      PointwiseEqual
        (arrow-map (C._after_ g f))
        (λ x → arrow-map g (arrow-map f x))

Full :
  {o h r m : Level} →
  {Object : Set o} →
  {R : Set r} →
  {category : Category {o} {h} Object} →
  {ring : Ring R} →
  FunctorToModules {m = m} category ring →
  Set (o ⊔ h ⊔ r ⊔ m)
Full {Object = Object} {category = category} functor =
  (A B : Object) →
  (function :
    ModuleObject.Carrier (FunctorToModules.object-map functor A) →
    ModuleObject.Carrier (FunctorToModules.object-map functor B)) →
  IsLinear
    (FunctorToModules.object-map functor A)
    (FunctorToModules.object-map functor B)
    function →
  Σ (Category.Hom category A B)
    (λ f →
      PointwiseEqual
        (FunctorToModules.arrow-map functor f)
        function)

Faithful :
  {o h r m : Level} →
  {Object : Set o} →
  {R : Set r} →
  {category : Category {o} {h} Object} →
  {ring : Ring R} →
  FunctorToModules {m = m} category ring →
  Set (o ⊔ h ⊔ m)
Faithful {Object = Object} {category = category} functor =
  (A B : Object) →
  (f g : Category.Hom category A B) →
  PointwiseEqual
    (FunctorToModules.arrow-map functor f)
    (FunctorToModules.arrow-map functor g) →
  f ≡ g

record ModuleCone
  {jo jh o h r m : Level}
  {Index : Set jo}
  {Object : Set o}
  {R : Set r}
  {index-category : Category {jo} {jh} Index}
  {category : Category {o} {h} Object}
  {ring : Ring R}
  (functor : FunctorToModules {m = m} category ring)
  (diagram : Diagram index-category category)
  (apex : ModuleObject ring m) :
  Set (jo ⊔ jh ⊔ o ⊔ h ⊔ r ⊔ m) where

  private
    module J = Category index-category
    module D = Diagram diagram
    module F = FunctorToModules functor

  field
    leg :
      (i : Index) →
      ModuleObject.Carrier apex →
      ModuleObject.Carrier (F.object-map (D.object-map i))
    leg-linear :
      (i : Index) →
      IsLinear apex (F.object-map (D.object-map i)) (leg i)
    natural :
      {i j : Index} →
      (f : J.Hom i j) →
      (x : ModuleObject.Carrier apex) →
      F.arrow-map (D.arrow-map f) (leg i x) ≡ leg j x

record MappedConeIsLimit
  {jo jh o h r m : Level}
  {Index : Set jo}
  {Object : Set o}
  {R : Set r}
  {index-category : Category {jo} {jh} Index}
  {category : Category {o} {h} Object}
  {ring : Ring R}
  {diagram : Diagram index-category category}
  {apex : Object}
  (functor : FunctorToModules {m = m} category ring)
  (cone : Cone diagram apex) :
  Set (jo ⊔ jh ⊔ o ⊔ h ⊔ r ⊔ lsuc m) where

  private
    module J = Category index-category
    module D = Diagram diagram
    module F = FunctorToModules functor

  field
    mapped-cone-natural :
      {i j : Index} →
      (f : J.Hom i j) →
      (x : ModuleObject.Carrier (F.object-map apex)) →
      F.arrow-map (D.arrow-map f)
        (F.arrow-map (Cone.leg cone i) x)
      ≡
      F.arrow-map (Cone.leg cone j) x
    universal :
      (other-apex : ModuleObject ring m) →
      (other : ModuleCone functor diagram other-apex) →
      Σ
        (ModuleObject.Carrier other-apex →
         ModuleObject.Carrier (F.object-map apex))
        (λ factor →
          IsLinear other-apex (F.object-map apex) factor
          ×
          (((i : Index) →
            (x : ModuleObject.Carrier other-apex) →
            F.arrow-map (Cone.leg cone i) (factor x) ≡
            ModuleCone.leg other i x)
          ×
          ((candidate :
              ModuleObject.Carrier other-apex →
              ModuleObject.Carrier (F.object-map apex)) →
            IsLinear other-apex (F.object-map apex) candidate →
            ((i : Index) →
              (x : ModuleObject.Carrier other-apex) →
              F.arrow-map (Cone.leg cone i) (candidate x) ≡
              ModuleCone.leg other i x) →
            PointwiseEqual candidate factor)))

record ModuleCocone
  {jo jh o h r m : Level}
  {Index : Set jo}
  {Object : Set o}
  {R : Set r}
  {index-category : Category {jo} {jh} Index}
  {category : Category {o} {h} Object}
  {ring : Ring R}
  (functor : FunctorToModules {m = m} category ring)
  (diagram : Diagram index-category category)
  (apex : ModuleObject ring m) :
  Set (jo ⊔ jh ⊔ o ⊔ h ⊔ r ⊔ m) where

  private
    module J = Category index-category
    module D = Diagram diagram
    module F = FunctorToModules functor

  field
    leg :
      (i : Index) →
      ModuleObject.Carrier (F.object-map (D.object-map i)) →
      ModuleObject.Carrier apex
    leg-linear :
      (i : Index) →
      IsLinear (F.object-map (D.object-map i)) apex (leg i)
    natural :
      {i j : Index} →
      (f : J.Hom i j) →
      (x :
        ModuleObject.Carrier (F.object-map (D.object-map i))) →
      leg j (F.arrow-map (D.arrow-map f) x) ≡ leg i x

record MappedCoconeIsColimit
  {jo jh o h r m : Level}
  {Index : Set jo}
  {Object : Set o}
  {R : Set r}
  {index-category : Category {jo} {jh} Index}
  {category : Category {o} {h} Object}
  {ring : Ring R}
  {diagram : Diagram index-category category}
  {apex : Object}
  (functor : FunctorToModules {m = m} category ring)
  (cocone : Cocone diagram apex) :
  Set (jo ⊔ jh ⊔ o ⊔ h ⊔ r ⊔ lsuc m) where

  private
    module J = Category index-category
    module D = Diagram diagram
    module F = FunctorToModules functor

  field
    mapped-cocone-natural :
      {i j : Index} →
      (f : J.Hom i j) →
      (x :
        ModuleObject.Carrier (F.object-map (D.object-map i))) →
      F.arrow-map (Cocone.leg cocone j)
        (F.arrow-map (D.arrow-map f) x)
      ≡
      F.arrow-map (Cocone.leg cocone i) x
    universal :
      (other-apex : ModuleObject ring m) →
      (other : ModuleCocone functor diagram other-apex) →
      Σ
        (ModuleObject.Carrier (F.object-map apex) →
         ModuleObject.Carrier other-apex)
        (λ factor →
          IsLinear (F.object-map apex) other-apex factor
          ×
          (((i : Index) →
            (x :
              ModuleObject.Carrier
                (F.object-map (D.object-map i))) →
            factor (F.arrow-map (Cocone.leg cocone i) x) ≡
            ModuleCocone.leg other i x)
          ×
          ((candidate :
              ModuleObject.Carrier (F.object-map apex) →
              ModuleObject.Carrier other-apex) →
            IsLinear (F.object-map apex) other-apex candidate →
            ((i : Index) →
              (x :
                ModuleObject.Carrier
                  (F.object-map (D.object-map i))) →
              candidate (F.arrow-map (Cocone.leg cocone i) x) ≡
              ModuleCocone.leg other i x) →
            PointwiseEqual candidate factor)))

PreservesFiniteLimits :
  {o h r m : Level} →
  {Object : Set o} →
  {R : Set r} →
  {category : Category {o} {h} Object} →
  {ring : Ring R} →
  FunctorToModules {m = m} category ring →
  Setω
PreservesFiniteLimits {Object = Object} functor =
  ∀ {jo jh : Level} →
  {Index : Set jo} →
  (index-category : Category {jo} {jh} Index) →
  FiniteCategory index-category →
  (diagram : Diagram index-category _) →
  (apex : Object) →
  (cone : Cone diagram apex) →
  IsLimit cone →
  MappedConeIsLimit functor cone

PreservesFiniteColimits :
  {o h r m : Level} →
  {Object : Set o} →
  {R : Set r} →
  {category : Category {o} {h} Object} →
  {ring : Ring R} →
  FunctorToModules {m = m} category ring →
  Setω
PreservesFiniteColimits {Object = Object} functor =
  ∀ {jo jh : Level} →
  {Index : Set jo} →
  (index-category : Category {jo} {jh} Index) →
  FiniteCategory index-category →
  (diagram : Diagram index-category _) →
  (apex : Object) →
  (cocone : Cocone diagram apex) →
  IsColimit cocone →
  MappedCoconeIsColimit functor cocone

record MitchellEmbedding
  {o h : Level}
  {Object : Set o}
  (category : Category {o} {h} Object) :
  Setω where

  field
    RingCarrier : Set (o ⊔ h)
    ring :
      Ring RingCarrier
    functor :
      FunctorToModules
        {m = o ⊔ h}
        category
        ring
    full :
      Full functor
    faithful :
      Faithful functor
    preserves-finite-limits :
      PreservesFiniteLimits functor
    preserves-finite-colimits :
      PreservesFiniteColimits functor

mitchell-s-embedding-theorem : Setω
mitchell-s-embedding-theorem =
  ∀ {o h : Level} →
  (Object : Set o) →
  (category : Category {o} {h} Object) →
  AbelianCategory category →
  MitchellEmbedding category
