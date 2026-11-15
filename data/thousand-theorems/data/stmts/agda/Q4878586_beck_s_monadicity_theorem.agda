-- Statement-only formalization of thousand-theorems corpus artifact Q4878586,
-- "Beck's monadicity theorem": a right adjoint that creates coequalizers of
-- all pairs split by that right adjoint is monadic. This file contains no proof.

{-# OPTIONS --safe #-}

module Q4878586_beck_s_monadicity_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_; Setω)
open import Agda.Builtin.Equality using (_≡_)
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
      (f : Hom C D) →
      (g : Hom B C) →
      (k : Hom A B) →
      f after (g after k) ≡ (f after g) after k
    identity-left :
      {A B : Object} →
      (f : Hom A B) →
      identity B after f ≡ f
    identity-right :
      {A B : Object} →
      (f : Hom A B) →
      f after identity A ≡ f

record Functor
  {oC hC oD hD : Level}
  {CObject : Set oC}
  {DObject : Set oD}
  (C : Category {oC} {hC} CObject)
  (D : Category {oD} {hD} DObject) :
  Set (oC ⊔ hC ⊔ oD ⊔ hD) where

  private
    module C = Category C
    module D = Category D

  field
    object : CObject → DObject
    arrow  :
      {A B : CObject} →
      C.Hom A B →
      D.Hom (object A) (object B)
    map-identity :
      (A : CObject) →
      arrow (C.identity A) ≡ D.identity (object A)
    map-compose :
      {A B E : CObject} →
      (f : C.Hom B E) →
      (g : C.Hom A B) →
      arrow (C._after_ f g) ≡
      D._after_ (arrow f) (arrow g)

record CategoryIso
  {o h : Level}
  {Object : Set o}
  (C : Category {o} {h} Object)
  (A B : Object) :
  Set (o ⊔ h) where

  private
    module C = Category C

  field
    forward  : C.Hom A B
    backward : C.Hom B A
    backward-after-forward :
      C._after_ backward forward ≡
      C.identity A
    forward-after-backward :
      C._after_ forward backward ≡
      C.identity B

record IsCoequalizer
  {o h : Level}
  {Object : Set o}
  (C : Category {o} {h} Object)
  {A B Q : Object}
  (f g : Category.Hom C A B)
  (quotient : Category.Hom C B Q) :
  Set (o ⊔ h) where

  private
    module C = Category C

  field
    coequalizes :
      C._after_ quotient f ≡
      C._after_ quotient g
    universal :
      (X : Object) →
      (candidate : C.Hom B X) →
      C._after_ candidate f ≡
      C._after_ candidate g →
      Σ (C.Hom Q X)
        (λ factor →
          C._after_ factor quotient ≡ candidate
          ×
          ((other : C.Hom Q X) →
            C._after_ other quotient ≡ candidate →
            other ≡ factor))

record SplitCoequalizer
  {o h : Level}
  {Object : Set o}
  (C : Category {o} {h} Object)
  {A B : Object}
  (f g : Category.Hom C A B) :
  Set (o ⊔ h) where

  private
    module C = Category C

  field
    object    : Object
    quotient  : C.Hom B object
    section   : C.Hom object B
    splitting : C.Hom B A

    coequalizes :
      C._after_ quotient f ≡
      C._after_ quotient g
    quotient-section :
      C._after_ quotient section ≡
      C.identity object
    first-splitting :
      C._after_ f splitting ≡
      C.identity B
    second-splitting :
      C._after_ g splitting ≡
      C._after_ section quotient

record CreatedCoequalizer
  {oC oD h : Level}
  {CObject : Set oC}
  {DObject : Set oD}
  (C : Category {oC} {h} CObject)
  (D : Category {oD} {h} DObject)
  (G : Functor D C)
  {A B : DObject}
  (f g : Category.Hom D A B)
  {target : CObject}
  (target-quotient :
    Category.Hom C (Functor.object G B) target) :
  Set (oC ⊔ oD ⊔ h) where

  private
    module C = Category C
    module D = Category D
    module G = Functor G

  field
    object   : DObject
    quotient : D.Hom B object
    is-coequalizer :
      IsCoequalizer D f g quotient
    image-comparison :
      CategoryIso C (G.object object) target
    image-quotient :
      C._after_
        (CategoryIso.forward image-comparison)
        (G.arrow quotient)
      ≡
      target-quotient

record CreatesGSplitCoequalizers
  {oC oD h : Level}
  {CObject : Set oC}
  {DObject : Set oD}
  (C : Category {oC} {h} CObject)
  (D : Category {oD} {h} DObject)
  (G : Functor D C) :
  Set (oC ⊔ oD ⊔ h) where

  private
    module C = Category C
    module D = Category D
    module G = Functor G

  field
    lifts-coequalizers :
      {A B : DObject} →
      (f g : D.Hom A B) →
      SplitCoequalizer C (G.arrow f) (G.arrow g) →
      {target : CObject} →
      (target-quotient : C.Hom (G.object B) target) →
      IsCoequalizer C
        (G.arrow f)
        (G.arrow g)
        target-quotient →
      CreatedCoequalizer C D G f g target-quotient

    reflects-coequalizers :
      {A B Q : DObject} →
      (f g : D.Hom A B) →
      SplitCoequalizer C (G.arrow f) (G.arrow g) →
      (quotient : D.Hom B Q) →
      D._after_ quotient f ≡
      D._after_ quotient g →
      IsCoequalizer C
        (G.arrow f)
        (G.arrow g)
        (G.arrow quotient) →
      IsCoequalizer D f g quotient

record Adjunction
  {oC oD h : Level}
  {CObject : Set oC}
  {DObject : Set oD}
  (C : Category {oC} {h} CObject)
  (D : Category {oD} {h} DObject)
  (F : Functor C D)
  (G : Functor D C) :
  Set (oC ⊔ oD ⊔ h) where

  private
    module C = Category C
    module D = Category D
    module F = Functor F
    module G = Functor G

  field
    unit :
      (A : CObject) →
      C.Hom A (G.object (F.object A))
    unit-natural :
      {A B : CObject} →
      (f : C.Hom A B) →
      C._after_ (G.arrow (F.arrow f)) (unit A) ≡
      C._after_ (unit B) f

    counit :
      (A : DObject) →
      D.Hom (F.object (G.object A)) A
    counit-natural :
      {A B : DObject} →
      (f : D.Hom A B) →
      D._after_ f (counit A) ≡
      D._after_ (counit B) (F.arrow (G.arrow f))

    left-triangle :
      (A : CObject) →
      D._after_
        (counit (F.object A))
        (F.arrow (unit A))
      ≡
      D.identity (F.object A)
    right-triangle :
      (A : DObject) →
      C._after_
        (G.arrow (counit A))
        (unit (G.object A))
      ≡
      C.identity (G.object A)

record AdjunctionAlgebra
  {oC oD h : Level}
  {CObject : Set oC}
  {DObject : Set oD}
  {C : Category {oC} {h} CObject}
  {D : Category {oD} {h} DObject}
  {F : Functor C D}
  {G : Functor D C}
  (adjunction : Adjunction C D F G) :
  Set (oC ⊔ oD ⊔ h) where

  private
    module C = Category C
    module F = Functor F
    module G = Functor G
    module A = Adjunction adjunction

  field
    carrier : CObject
    action :
      C.Hom
        (G.object (F.object carrier))
        carrier
    unit-law :
      C._after_ action (A.unit carrier) ≡
      C.identity carrier
    associativity-law :
      C._after_
        action
        (G.arrow (F.arrow action))
      ≡
      C._after_
        action
        (G.arrow (A.counit (F.object carrier)))

AlgebraHom :
  {oC oD h : Level} →
  {CObject : Set oC} →
  {DObject : Set oD} →
  {C : Category {oC} {h} CObject} →
  {D : Category {oD} {h} DObject} →
  {F : Functor C D} →
  {G : Functor D C} →
  (adjunction : Adjunction C D F G) →
  (A B : AdjunctionAlgebra adjunction) →
  Category.Hom C
    (AdjunctionAlgebra.carrier A)
    (AdjunctionAlgebra.carrier B) →
  Set h
AlgebraHom {C = C} {F = F} {G = G} adjunction A B f =
  Category._after_ C f (AdjunctionAlgebra.action A) ≡
  Category._after_ C
    (AdjunctionAlgebra.action B)
    (Functor.arrow G (Functor.arrow F f))

ComparisonHom :
  {oC oD h : Level} →
  {CObject : Set oC} →
  {DObject : Set oD} →
  {C : Category {oC} {h} CObject} →
  {D : Category {oD} {h} DObject} →
  {F : Functor C D} →
  {G : Functor D C} →
  (adjunction : Adjunction C D F G) →
  (A B : DObject) →
  Category.Hom C
    (Functor.object G A)
    (Functor.object G B) →
  Set h
ComparisonHom {C = C} {F = F} {G = G} adjunction A B f =
  Category._after_ C
    f
    (Functor.arrow G (Adjunction.counit adjunction A))
  ≡
  Category._after_ C
    (Functor.arrow G (Adjunction.counit adjunction B))
    (Functor.arrow G (Functor.arrow F f))

record AlgebraIsoToComparison
  {oC oD h : Level}
  {CObject : Set oC}
  {DObject : Set oD}
  {C : Category {oC} {h} CObject}
  {D : Category {oD} {h} DObject}
  {F : Functor C D}
  {G : Functor D C}
  (adjunction : Adjunction C D F G)
  (algebra : AdjunctionAlgebra adjunction)
  (object : DObject) :
  Set (oC ⊔ oD ⊔ h) where

  private
    module C = Category C
    module F = Functor F
    module G = Functor G
    module A = Adjunction adjunction
    module X = AdjunctionAlgebra algebra

  field
    forward  : C.Hom X.carrier (G.object object)
    backward : C.Hom (G.object object) X.carrier

    forward-is-algebra-hom :
      C._after_ forward X.action ≡
      C._after_
        (G.arrow (A.counit object))
        (G.arrow (F.arrow forward))
    backward-is-algebra-hom :
      C._after_
        backward
        (G.arrow (A.counit object))
      ≡
      C._after_
        X.action
        (G.arrow (F.arrow backward))

    backward-after-forward :
      C._after_ backward forward ≡
      C.identity X.carrier
    forward-after-backward :
      C._after_ forward backward ≡
      C.identity (G.object object)

record ComparisonIsEquivalence
  {oC oD h : Level}
  {CObject : Set oC}
  {DObject : Set oD}
  (C : Category {oC} {h} CObject)
  (D : Category {oD} {h} DObject)
  (F : Functor C D)
  (G : Functor D C)
  (adjunction : Adjunction C D F G) :
  Set (oC ⊔ oD ⊔ h) where

  private
    module C = Category C
    module D = Category D
    module F = Functor F
    module G = Functor G

  field
    faithful :
      {A B : DObject} →
      (f g : D.Hom A B) →
      G.arrow f ≡ G.arrow g →
      f ≡ g

    full :
      {A B : DObject} →
      (f : C.Hom (G.object A) (G.object B)) →
      ComparisonHom adjunction A B f →
      Σ (D.Hom A B)
        (λ lift → G.arrow lift ≡ f)

    essentially-surjective :
      (algebra : AdjunctionAlgebra adjunction) →
      Σ DObject
        (λ object →
          AlgebraIsoToComparison adjunction algebra object)

record MonadicRightAdjoint
  {oC oD h : Level}
  {CObject : Set oC}
  {DObject : Set oD}
  (C : Category {oC} {h} CObject)
  (D : Category {oD} {h} DObject)
  (G : Functor D C) :
  Set (oC ⊔ oD ⊔ h) where

  field
    left-adjoint : Functor C D
    adjunction :
      Adjunction C D left-adjoint G
    comparison-is-equivalence :
      ComparisonIsEquivalence
        C D left-adjoint G adjunction

beck-s-monadicity-theorem : Setω
beck-s-monadicity-theorem =
  ∀ {oC oD h : Level} →
  (CObject : Set oC) →
  (DObject : Set oD) →
  (C : Category {oC} {h} CObject) →
  (D : Category {oD} {h} DObject) →
  (G : Functor D C) →
  (F : Functor C D) →
  Adjunction C D F G →
  CreatesGSplitCoequalizers C D G →
  MonadicRightAdjoint C D G
