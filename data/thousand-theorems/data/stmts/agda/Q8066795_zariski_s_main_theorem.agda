-- Statement-only formalization of Thousand Theorems artifact Q8066795,
-- “Zariski's main theorem”: a proper scheme morphism with finite point-fiber
-- is finite over an open neighborhood of that point. This file contains no proof.

{-# OPTIONS --safe #-}

module Q8066795_zariski_s_main_theorem where

open import Agda.Primitive using (Level; Setω; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 4 _,_
infixr 3 _×_
infix  1 _↔_

record ⊥ : Set where

record ⊤ {a : Level} : Set a where
  constructor tt

¬_ : ∀ {a} → Set a → Set a
¬ A = A → ⊥

transport :
  ∀ {a b} {A : Set a}
  (P : A → Set b) {x y : A} →
  x ≡ y → P x → P y
transport P {x = x} {.x} refl px = px

record _×_ {a b : Level} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    first  : A
    second : B

-- A conventional disjoint sum, presented without importing a library.
data Either {a b : Level} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  left  : A → Either A B
  right : B → Either A B

record _↔_ {a b : Level} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor iff
  field
    forward  : A → B
    backward : B → A

record Σ {a b : Level} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst

syntax Σ A (λ x → B) = Σ[ x ∈ A ] B

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (suc n)
  fsuc  : {n : Nat} → Fin n → Fin (suc n)

record Bijection {a b : Level} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    to       : A → B
    from     : B → A
    from-to  : (x : A) → from (to x) ≡ x
    to-from  : (y : B) → to (from y) ≡ y

record Finite {a : Level} (A : Set a) : Set a where
  field
    cardinality : Nat
    enumerate   : Bijection A (Fin cardinality)

record CommutativeRing (a : Level) : Set (lsuc a) where
  field
    Carrier : Set a
    0# 1#   : Carrier
    _+_ _*_ : Carrier → Carrier → Carrier
    -_      : Carrier → Carrier

    +-associative : (x y z : Carrier) → (x + y) + z ≡ x + (y + z)
    +-commutative : (x y : Carrier) → x + y ≡ y + x
    +-identity    : (x : Carrier) → x + 0# ≡ x
    +-inverse     : (x : Carrier) → x + (- x) ≡ 0#

    *-associative : (x y z : Carrier) → (x * y) * z ≡ x * (y * z)
    *-commutative : (x y : Carrier) → x * y ≡ y * x
    *-identity    : (x : Carrier) → x * 1# ≡ x
    *-distributes : (x y z : Carrier) → x * (y + z) ≡ (x * y) + (x * z)

open CommutativeRing

record RingHom {a b : Level}
               (R : CommutativeRing a)
               (S : CommutativeRing b) : Set (a ⊔ b) where
  field
    map       : Carrier R → Carrier S
    map-zero  : map (0# R) ≡ 0# S
    map-one   : map (1# R) ≡ 1# S
    map-add   : (x y : Carrier R) → map (_+_ R x y) ≡ _+_ S (map x) (map y)
    map-mul   : (x y : Carrier R) → map (_*_ R x y) ≡ _*_ S (map x) (map y)
    map-neg   : (x : Carrier R) → map (-_ R x) ≡ -_ S (map x)

open RingHom

record RingEquivalence {a b : Level}
                       (R : CommutativeRing a)
                       (S : CommutativeRing b) : Set (a ⊔ b) where
  field
    hom       : RingHom R S
    inverse   : RingHom S R
    left-law  : (x : Carrier R) → map inverse (map hom x) ≡ x
    right-law : (y : Carrier S) → map hom (map inverse y) ≡ y

record Unit {a : Level} (R : CommutativeRing a) (x : Carrier R) : Set a where
  field
    inverse       : Carrier R
    inverse-left  : _*_ R inverse x ≡ 1# R
    inverse-right : _*_ R x inverse ≡ 1# R

record LocalRing {a : Level} (R : CommutativeRing a) : Set a where
  field
    local-unit-law :
      (x : Carrier R) →
      Either (Unit R x) (Unit R (_+_ R (1# R) (-_ R x)))

record LocalRingHom {a b : Level}
                    {R : CommutativeRing a}
                    {S : CommutativeRing b}
                    (localR : LocalRing R)
                    (localS : LocalRing S)
                    (φ : RingHom R S) : Set (a ⊔ b) where
  field
    reflects-units :
      (x : Carrier R) → Unit S (map φ x) → Unit R x

data GeneratedSubring {a b c : Level}
     {R : CommutativeRing a}
     {S : CommutativeRing b}
     (φ : RingHom R S)
     {I : Set c}
     (generators : I → Carrier S) : Carrier S → Set (a ⊔ b ⊔ c) where
  image     : (r : Carrier R) → GeneratedSubring φ generators (map φ r)
  generator : (i : I) → GeneratedSubring φ generators (generators i)
  add       : ∀ {x y} →
              GeneratedSubring φ generators x →
              GeneratedSubring φ generators y →
              GeneratedSubring φ generators (_+_ S x y)
  multiply  : ∀ {x y} →
              GeneratedSubring φ generators x →
              GeneratedSubring φ generators y →
              GeneratedSubring φ generators (_*_ S x y)
  negate    : ∀ {x} →
              GeneratedSubring φ generators x →
              GeneratedSubring φ generators (-_ S x)

record FiniteTypeRingHom {a b : Level}
                         {R : CommutativeRing a}
                         {S : CommutativeRing b}
                         (φ : RingHom R S) : Set (a ⊔ b) where
  field
    generator-count : Nat
    generators      : Fin generator-count → Carrier S
    generates       :
      (s : Carrier S) → GeneratedSubring φ generators s

data ModuleSpan {a b c : Level}
     {R : CommutativeRing a}
     {S : CommutativeRing b}
     (φ : RingHom R S)
     {I : Set c}
     (generators : I → Carrier S) : Carrier S → Set (a ⊔ b ⊔ c) where
  zero      : ModuleSpan φ generators (0# S)
  generator : (i : I) → ModuleSpan φ generators (generators i)
  add       : ∀ {x y} →
              ModuleSpan φ generators x →
              ModuleSpan φ generators y →
              ModuleSpan φ generators (_+_ S x y)
  scale     : (r : Carrier R) → ∀ {x} →
              ModuleSpan φ generators x →
              ModuleSpan φ generators (_*_ S (map φ r) x)

record FiniteRingHom {a b : Level}
                     {R : CommutativeRing a}
                     {S : CommutativeRing b}
                     (φ : RingHom R S) : Set (a ⊔ b) where
  field
    generator-count : Nat
    generators      : Fin generator-count → Carrier S
    spans           : (s : Carrier S) → ModuleSpan φ generators s

record Ideal {a : Level} (R : CommutativeRing a) : Set (lsuc a) where
  field
    member         : Carrier R → Set a
    contains-zero  : member (0# R)
    closed-add     : ∀ {x y} → member x → member y → member (_+_ R x y)
    closed-neg     : ∀ {x} → member x → member (-_ R x)
    absorbs        : (r : Carrier R) → ∀ {x} → member x → member (_*_ R r x)

record PrimeIdeal {a : Level} (R : CommutativeRing a) : Set (lsuc a) where
  field
    ideal      : Ideal R
    proper     : ¬ Ideal.member ideal (1# R)
    prime      : (x y : Carrier R) →
                 Ideal.member ideal (_*_ R x y) →
                 Either (Ideal.member ideal x) (Ideal.member ideal y)

record TopologicalSpace (a : Level) : Set (lsuc a) where
  field
    Point  : Set a
    IsOpen : (Point → Set a) → Set a

    open-extensional :
      (U V : Point → Set a) →
      ((x : Point) → U x ↔ V x) →
      IsOpen U → IsOpen V

    whole-open :
      IsOpen (λ _ → ⊤)

    intersection-open :
      ∀ {U V} → IsOpen U → IsOpen V →
      IsOpen (λ x → U x × V x)

    union-open :
      {I : Set a} (U : I → Point → Set a) →
      ((i : I) → IsOpen (U i)) →
      IsOpen (λ x → Σ[ i ∈ I ] U i x)

open TopologicalSpace

record OpenSubset {a : Level} (T : TopologicalSpace a) : Set (lsuc a) where
  field
    contains : Point T → Set a
    is-open  : IsOpen T contains

open OpenSubset

_∈_ : ∀ {a} {T : TopologicalSpace a} → Point T → OpenSubset T → Set a
x ∈ U = contains U x

record OpenSame {a : Level} {T : TopologicalSpace a}
                (U V : OpenSubset T) : Set a where
  field
    membership-equivalent :
      (x : Point T) → (x ∈ U) ↔ (x ∈ V)

openSame-reflexive :
  ∀ {a} {T : TopologicalSpace a}
  (U : OpenSubset T) → OpenSame U U
OpenSame.membership-equivalent (openSame-reflexive U) x =
  iff (λ u → u) (λ u → u)

openSame-transitive :
  ∀ {a} {T : TopologicalSpace a}
  {U V W : OpenSubset T} →
  OpenSame U V → OpenSame V W → OpenSame U W
OpenSame.membership-equivalent (openSame-transitive eUV eVW) x =
  iff
    (λ u → _↔_.forward
      (OpenSame.membership-equivalent eVW x)
      (_↔_.forward (OpenSame.membership-equivalent eUV x) u))
    (λ w → _↔_.backward
      (OpenSame.membership-equivalent eUV x)
      (_↔_.backward (OpenSame.membership-equivalent eVW x) w))

Included : ∀ {a} {T : TopologicalSpace a} → OpenSubset T → OpenSubset T → Set a
Included {T = T} U V = (x : Point T) → x ∈ U → x ∈ V

record OpenCover {a : Level}
                 {T : TopologicalSpace a}
                 (U : OpenSubset T) : Set (lsuc a) where
  field
    Index   : Set a
    member  : Index → OpenSubset T
    inside  : (i : Index) → Included (member i) U
    covers  : (x : Point T) →
              (x ∈ U) ↔ Σ[ i ∈ Index ] (x ∈ member i)

record SheafOfRings {a : Level} (T : TopologicalSpace a) : Setω where
  field
    Sections : OpenSubset T → CommutativeRing a

    sections-extensional :
      {U V : OpenSubset T} →
      OpenSame U V →
      RingEquivalence (Sections U) (Sections V)

    sections-extensional-independent :
      {U V : OpenSubset T}
      (e₁ e₂ : OpenSame U V)
      (s : Carrier (Sections U)) →
      map (RingEquivalence.hom (sections-extensional e₁)) s ≡
      map (RingEquivalence.hom (sections-extensional e₂)) s

    sections-extensional-reflexive :
      (U : OpenSubset T)
      (s : Carrier (Sections U)) →
      map
        (RingEquivalence.hom
          (sections-extensional (openSame-reflexive U))) s ≡ s

    sections-extensional-composition :
      {U V W : OpenSubset T}
      (eUV : OpenSame U V)
      (eVW : OpenSame V W)
      (s : Carrier (Sections U)) →
      map (RingEquivalence.hom (sections-extensional eVW))
          (map (RingEquivalence.hom (sections-extensional eUV)) s) ≡
      map
        (RingEquivalence.hom
          (sections-extensional (openSame-transitive eUV eVW))) s

    restrict :
      {U V : OpenSubset T} →
      Included U V →
      RingHom (Sections V) (Sections U)

    restrict-independent :
      {U V : OpenSubset T}
      (i j : Included U V)
      (s : Carrier (Sections V)) →
      map (restrict {U = U} {V = V} i) s ≡
      map (restrict {U = U} {V = V} j) s

    sections-extensional-restrict :
      {U U′ V V′ : OpenSubset T}
      (eU : OpenSame U U′)
      (eV : OpenSame V V′)
      (UV : Included U V)
      (U′V′ : Included U′ V′)
      (s : Carrier (Sections V)) →
      map (RingEquivalence.hom (sections-extensional eU))
          (map (restrict {U = U} {V = V} UV) s) ≡
      map (restrict {U = U′} {V = V′} U′V′)
          (map (RingEquivalence.hom (sections-extensional eV)) s)

    restrict-identity :
      (U : OpenSubset T) (s : Carrier (Sections U)) →
      map (restrict (λ _ u → u)) s ≡ s

    restrict-composition :
      {U V W : OpenSubset T}
      (UV : Included U V) (VW : Included V W)
      (s : Carrier (Sections W)) →
      map (restrict {U = U} {V = V} UV)
          (map (restrict {U = V} {V = W} VW) s) ≡
      map (restrict {U = U} {V = W}
             (λ x u → VW x (UV x u))) s

    glue :
      {U : OpenSubset T}
      (cover : OpenCover U)
      (local : (i : OpenCover.Index cover) →
               Carrier (Sections (OpenCover.member cover i))) →
      ((i j : OpenCover.Index cover) →
       (W : OpenSubset T) →
       (Wi : Included W (OpenCover.member cover i)) →
       (Wj : Included W (OpenCover.member cover j)) →
       map (restrict {U = W} {V = OpenCover.member cover i} Wi)
           (local i) ≡
       map (restrict {U = W} {V = OpenCover.member cover j} Wj)
           (local j)) →
      Carrier (Sections U)

    glue-restricts :
      {U : OpenSubset T}
      (cover : OpenCover U)
      (local : (i : OpenCover.Index cover) →
               Carrier (Sections (OpenCover.member cover i)))
      (compatible :
       (i j : OpenCover.Index cover) →
       (W : OpenSubset T) →
       (Wi : Included W (OpenCover.member cover i)) →
       (Wj : Included W (OpenCover.member cover j)) →
       map (restrict Wi) (local i) ≡
       map (restrict Wj) (local j)) →
      (i : OpenCover.Index cover) →
      map (restrict
             {U = OpenCover.member cover i} {V = U}
             (OpenCover.inside cover i))
          (glue cover local compatible)
        ≡ local i

    glue-unique :
      {U : OpenSubset T}
      (cover : OpenCover U)
      (s t : Carrier (Sections U)) →
      ((i : OpenCover.Index cover) →
       map (restrict
              {U = OpenCover.member cover i} {V = U}
              (OpenCover.inside cover i)) s ≡
       map (restrict
              {U = OpenCover.member cover i} {V = U}
              (OpenCover.inside cover i)) t) →
      s ≡ t

open SheafOfRings

record CommonRestriction {a : Level}
       {T : TopologicalSpace a}
       (O : SheafOfRings T)
       (x : Point T)
       (U V : OpenSubset T)
       (s : Carrier (Sections O U))
       (t : Carrier (Sections O V)) : Setω where
  field
    neighborhood : OpenSubset T
    at-point     : x ∈ neighborhood
    in-left      : Included neighborhood U
    in-right     : Included neighborhood V
    agrees       :
      map (restrict O {U = neighborhood} {V = U} in-left) s ≡
      map (restrict O {U = neighborhood} {V = V} in-right) t

record Stalk {a : Level}
             {T : TopologicalSpace a}
             (O : SheafOfRings T)
             (x : Point T) : Setω where
  field
    ring       : CommutativeRing a
    local-ring : LocalRing ring

    germ :
      (U : OpenSubset T) → x ∈ U →
      RingHom (Sections O U) ring

    germ-restricts :
      {U V : OpenSubset T}
      (UV : Included U V)
      (hx : x ∈ U)
      (s : Carrier (Sections O V)) →
      map (germ U hx)
          (map (restrict O {U = U} {V = V} UV) s) ≡
      map (germ V (UV x hx)) s

    represented :
      (z : Carrier ring) →
      Σ[ U ∈ OpenSubset T ]
        Σ[ hx ∈ (x ∈ U) ]
          Σ[ s ∈ Carrier (Sections O U) ]
            (map (germ U hx) s ≡ z)

    equal-locally :
      {U V : OpenSubset T}
      (hxU : x ∈ U) (hxV : x ∈ V)
      (s : Carrier (Sections O U))
      (t : Carrier (Sections O V)) →
      map (germ U hxU) s ≡ map (germ V hxV) t →
      CommonRestriction O x U V s t

record IsLocalizationAtElement {a : Level}
       {R S : CommutativeRing a}
       (φ : RingHom R S)
       (f : Carrier R) : Setω where
  field
    image-is-unit : Unit S (map φ f)

    factor :
      {b : Level} (T : CommutativeRing b)
      (ψ : RingHom R T) →
      Unit T (map ψ f) →
      RingHom S T

    factor-agrees :
      {b : Level} (T : CommutativeRing b)
      (ψ : RingHom R T)
      (unit-image : Unit T (map ψ f))
      (r : Carrier R) →
      map (factor T ψ unit-image) (map φ r) ≡ map ψ r

    factor-unique :
      {b : Level} (T : CommutativeRing b)
      (ψ : RingHom R T)
      (unit-image : Unit T (map ψ f))
      (h : RingHom S T) →
      ((r : Carrier R) → map h (map φ r) ≡ map ψ r) →
      (s : Carrier S) → map h s ≡ map (factor T ψ unit-image) s

record AffinePresentation {a : Level}
       {T : TopologicalSpace a}
       (O : SheafOfRings T)
       (U : OpenSubset T) : Setω where
  field
    point-prime :
      Bijection
        (Σ[ x ∈ Point T ] (x ∈ U))
        (PrimeIdeal (Sections O U))

    principal-open :
      Carrier (Sections O U) → OpenSubset T

    principal-inside :
      (f : Carrier (Sections O U)) →
      Included (principal-open f) U

    principal-membership :
      (f : Carrier (Sections O U))
      (p : Σ[ x ∈ Point T ] (x ∈ U)) →
      (Σ.fst p ∈ principal-open f) ↔
      ¬ Ideal.member
          (PrimeIdeal.ideal (Bijection.to point-prime p)) f

    principal-localization :
      (f : Carrier (Sections O U)) →
      IsLocalizationAtElement
        (restrict O {U = principal-open f} {V = U}
          (principal-inside f)) f

    principal-basis :
      (W : OpenSubset T) →
      Included W U →
      (x : Point T) → x ∈ W →
      Σ[ f ∈ Carrier (Sections O U) ]
        (x ∈ principal-open f × Included (principal-open f) W)

record AffineNeighborhood {a : Level}
       {T : TopologicalSpace a}
       (O : SheafOfRings T)
       (x : Point T) : Setω where
  field
    open-neighborhood : OpenSubset T
    contains-point    : x ∈ open-neighborhood
    is-affine         : AffinePresentation O open-neighborhood

record Scheme (a : Level) : Setω where
  field
    space          : TopologicalSpace a
    structureSheaf : SheafOfRings space
    stalk          : (x : Point space) → Stalk structureSheaf x
    stalk-extensional :
      {x y : Point space} →
      x ≡ y →
      RingEquivalence
        (Stalk.ring (stalk x))
        (Stalk.ring (stalk y))
    stalk-extensional-independent :
      {x y : Point space}
      (e₁ e₂ : x ≡ y)
      (z : Carrier (Stalk.ring (stalk x))) →
      map (RingEquivalence.hom (stalk-extensional e₁)) z ≡
      map (RingEquivalence.hom (stalk-extensional e₂)) z
    locally-affine :
      (x : Point space) →
      AffineNeighborhood structureSheaf x

open Scheme

MapsInto : ∀ {a} {X Y : Scheme a} →
           (Point (space X) → Point (space Y)) →
           OpenSubset (space X) → OpenSubset (space Y) → Set a
MapsInto {X = X} f U V =
  (x : Point (space X)) → x ∈ U → f x ∈ V

record SchemeHom {a : Level} (X Y : Scheme a) : Setω where
  field
    on-points : Point (space X) → Point (space Y)

    continuous :
      (V : OpenSubset (space Y)) →
      IsOpen (space X) (λ x → on-points x ∈ V)

    on-sections :
      (U : OpenSubset (space X))
      (V : OpenSubset (space Y)) →
      MapsInto {X = X} {Y = Y} on-points U V →
      RingHom (Sections (structureSheaf Y) V)
              (Sections (structureSheaf X) U)

    section-map-independent :
      (U : OpenSubset (space X))
      (V : OpenSubset (space Y))
      (h k : MapsInto {X = X} {Y = Y} on-points U V)
      (s : Carrier (Sections (structureSheaf Y) V)) →
      map (on-sections U V h) s ≡
      map (on-sections U V k) s

    section-naturality :
      {U₁ U₂ : OpenSubset (space X)}
      {V₁ V₂ : OpenSubset (space Y)}
      (U₁U₂ : Included U₁ U₂)
      (V₁V₂ : Included V₁ V₂)
      (h₁ : MapsInto {X = X} {Y = Y} on-points U₁ V₁)
      (h₂ : MapsInto {X = X} {Y = Y} on-points U₂ V₂)
      (s : Carrier (Sections (structureSheaf Y) V₂)) →
      map (restrict (structureSheaf X) U₁U₂)
          (map (on-sections U₂ V₂ h₂) s) ≡
      map (on-sections U₁ V₁ h₁)
          (map (restrict (structureSheaf Y) V₁V₂) s)

    on-stalks :
      (x : Point (space X)) →
      RingHom (Stalk.ring (stalk Y (on-points x)))
              (Stalk.ring (stalk X x))

    stalk-map-local :
      (x : Point (space X)) →
      LocalRingHom
        (Stalk.local-ring (stalk Y (on-points x)))
        (Stalk.local-ring (stalk X x))
        (on-stalks x)

    germ-compatible :
      (U : OpenSubset (space X))
      (V : OpenSubset (space Y))
      (h : MapsInto {X = X} {Y = Y} on-points U V)
      (x : Point (space X)) (hx : x ∈ U)
      (s : Carrier (Sections (structureSheaf Y) V)) →
      map (on-stalks x)
          (map (Stalk.germ (stalk Y (on-points x)) V (h x hx)) s) ≡
      map (Stalk.germ (stalk X x) U hx)
          (map (on-sections U V h) s)

open SchemeHom

record HomEquality {a : Level} {X Y : Scheme a}
                   (f g : SchemeHom X Y) : Setω where
  field
    points-agree :
      (x : Point (space X)) →
      on-points f x ≡ on-points g x

    sections-agree :
      (U : OpenSubset (space X))
      (V : OpenSubset (space Y))
      (hf : MapsInto {X = X} {Y = Y} (on-points f) U V)
      (hg : MapsInto {X = X} {Y = Y} (on-points g) U V)
      (s : Carrier (Sections (structureSheaf Y) V)) →
      map (on-sections f U V hf) s ≡
      map (on-sections g U V hg) s

inverseOpen : ∀ {a} {X Y : Scheme a} →
              SchemeHom X Y → OpenSubset (space Y) → OpenSubset (space X)
contains (inverseOpen f V) x = on-points f x ∈ V
is-open  (inverseOpen f V) = continuous f V

inverseMapsInto : ∀ {a} {X Y : Scheme a}
                  (f : SchemeHom X Y)
                  (V : OpenSubset (space Y)) →
                  MapsInto {X = X} {Y = Y}
                    (on-points f) (inverseOpen f V) V
inverseMapsInto f V x hx = hx

Image : ∀ {a b} {A : Set a} {B : Set b} →
        (A → B) → (A → Set a) → B → Set (a ⊔ b)
Image {A = A} f U y = Σ[ x ∈ A ] (U x × f x ≡ y)

IsClosed : ∀ {a} (T : TopologicalSpace a) →
           (Point T → Set a) → Set a
IsClosed T C = IsOpen T (λ x → ¬ C x)

record ClosedMap {a : Level}
                 {S T : TopologicalSpace a}
                 (f : Point S → Point T) : Setω where
  field
    maps-closed-to-closed :
      (C : Point S → Set a) →
      IsClosed S C →
      IsClosed T (Image f C)

record ClosedImmersion {a : Level}
                       {X Y : Scheme a}
                       (f : SchemeHom X Y) : Setω where
  field
    closed-image :
      IsClosed (space Y) (Image (on-points f) (λ _ → ⊤))

    point-injective :
      (x x′ : Point (space X)) →
      on-points f x ≡ on-points f x′ →
      x ≡ x′

    induced-topology :
      (U : OpenSubset (space X)) →
      Σ[ V ∈ OpenSubset (space Y) ]
        ((x : Point (space X)) →
         (x ∈ U) ↔ (on-points f x ∈ V))

    stalk-surjective :
      (x : Point (space X))
      (z : Carrier (Stalk.ring (stalk X x))) →
      Σ[ w ∈ Carrier
            (Stalk.ring (stalk Y (on-points f x))) ]
        (map (on-stalks f x) w ≡ z)

record OpenSubschemePresentation {a : Level}
       (X : Scheme a)
       (U : OpenSubset (space X))
       (XU : Scheme a)
       (inclusion : SchemeHom XU X) : Setω where
  field
    points :
      Bijection (Point (space XU))
                (Σ[ x ∈ Point (space X) ] (x ∈ U))

    inclusion-is-canonical :
      (x : Point (space XU)) →
      on-points inclusion x ≡ Σ.fst (Bijection.to points x)

    opens-from-ambient :
      (V : OpenSubset (space X)) →
      Included V U →
      OpenSubset (space XU)

    opens-to-ambient :
      OpenSubset (space XU) → OpenSubset (space X)

    ambient-open-inside :
      (W : OpenSubset (space XU)) →
      Included (opens-to-ambient W) U

    membership-agrees :
      (W : OpenSubset (space XU))
      (x : Point (space XU)) →
      (x ∈ W) ↔
      (Σ.fst (Bijection.to points x) ∈ opens-to-ambient W)

    ambient-opens-recovered :
      (V : OpenSubset (space X))
      (VU : Included V U)
      (x : Point (space XU)) →
      (x ∈ opens-from-ambient V VU) ↔
      (Σ.fst (Bijection.to points x) ∈ V)

    inclusion-maps-into :
      (W : OpenSubset (space XU)) →
      MapsInto {X = XU} {Y = X}
        (on-points inclusion) W (opens-to-ambient W)

    sections-agree :
      (W : OpenSubset (space XU)) →
      RingEquivalence
        (Sections (structureSheaf X)
                  (opens-to-ambient W))
        (Sections (structureSheaf XU) W)

    inclusion-sections-canonical :
      (W : OpenSubset (space XU))
      (s : Carrier
        (Sections (structureSheaf X) (opens-to-ambient W))) →
      map
        (on-sections inclusion W (opens-to-ambient W)
          (inclusion-maps-into W)) s ≡
      map (RingEquivalence.hom (sections-agree W)) s

    stalks-agree :
      (x : Point (space XU)) →
      RingEquivalence
        (Stalk.ring (stalk X (on-points inclusion x)))
        (Stalk.ring (stalk XU x))

    inclusion-stalks-canonical :
      (x : Point (space XU))
      (z : Carrier
        (Stalk.ring (stalk X (on-points inclusion x)))) →
      map (on-stalks inclusion x) z ≡
      map (RingEquivalence.hom (stalks-agree x)) z

record OpenSubschemeResult {a : Level}
       (X : Scheme a)
       (U : OpenSubset (space X)) : Setω where
  field
    object       : Scheme a
    inclusion    : SchemeHom object X
    presentation :
      OpenSubschemePresentation X U object inclusion

record SchemeCategory (a : Level) : Setω where
  field
    identity : (X : Scheme a) → SchemeHom X X
    compose  : {X Y Z : Scheme a} →
               SchemeHom Y Z → SchemeHom X Y → SchemeHom X Z

    identity-points :
      (X : Scheme a)
      (x : Point (space X)) →
      on-points (identity X) x ≡ x

    identity-sections :
      (X : Scheme a)
      (U V : OpenSubset (space X))
      (h : MapsInto {X = X} {Y = X}
        (on-points (identity X)) U V)
      (s : Carrier (Sections (structureSheaf X) V)) →
      map (on-sections (identity X) U V h) s ≡
      map
        (restrict (structureSheaf X)
          (λ x hx →
            transport
              (λ z → z ∈ V)
              (identity-points X x)
              (h x hx)))
        s

    identity-stalks :
      (X : Scheme a)
      (x : Point (space X))
      (z : Carrier
        (Stalk.ring
          (stalk X (on-points (identity X) x)))) →
      map (on-stalks (identity X) x) z ≡
      map
        (RingEquivalence.hom
          (stalk-extensional X (identity-points X x)))
        z

    compose-points :
      {X Y Z : Scheme a}
      (g : SchemeHom Y Z)
      (f : SchemeHom X Y)
      (x : Point (space X)) →
      on-points (compose g f) x ≡
      on-points g (on-points f x)

    compose-sections :
      {X Y Z : Scheme a}
      (g : SchemeHom Y Z)
      (f : SchemeHom X Y)
      (U : OpenSubset (space X))
      (W : OpenSubset (space Z))
      (h : MapsInto {X = X} {Y = Z}
        (on-points (compose g f)) U W)
      (s : Carrier (Sections (structureSheaf Z) W)) →
      map (on-sections (compose g f) U W h) s ≡
      map
        (on-sections f U (inverseOpen g W)
          (λ x hx →
            transport
              (λ z → z ∈ W)
              (compose-points g f x)
              (h x hx)))
        (map
          (on-sections g (inverseOpen g W) W
            (inverseMapsInto g W))
          s)

    compose-stalks :
      {X Y Z : Scheme a}
      (g : SchemeHom Y Z)
      (f : SchemeHom X Y)
      (x : Point (space X))
      (z : Carrier
        (Stalk.ring
          (stalk Z (on-points (compose g f) x)))) →
      map (on-stalks (compose g f) x) z ≡
      map (on-stalks f x)
        (map (on-stalks g (on-points f x))
          (map
            (RingEquivalence.hom
              (stalk-extensional Z (compose-points g f x)))
            z))

    left-identity  :
      {X Y : Scheme a} (f : SchemeHom X Y) →
      HomEquality (compose (identity Y) f) f
    right-identity :
      {X Y : Scheme a} (f : SchemeHom X Y) →
      HomEquality (compose f (identity X)) f
    associative :
      {W X Y Z : Scheme a}
      (h : SchemeHom Y Z)
      (g : SchemeHom X Y)
      (f : SchemeHom W X) →
      HomEquality (compose h (compose g f)) (compose (compose h g) f)

    pullback-object :
      {X Y Z : Scheme a}
      (f : SchemeHom X Z)
      (g : SchemeHom Y Z) →
      Scheme a

    pullback-left :
      {X Y Z : Scheme a}
      (f : SchemeHom X Z)
      (g : SchemeHom Y Z) →
      SchemeHom (pullback-object f g) X

    pullback-right :
      {X Y Z : Scheme a}
      (f : SchemeHom X Z)
      (g : SchemeHom Y Z) →
      SchemeHom (pullback-object f g) Y

    pullback-commutes :
      {X Y Z : Scheme a}
      (f : SchemeHom X Z)
      (g : SchemeHom Y Z) →
      HomEquality
        (compose f (pullback-left f g))
        (compose g (pullback-right f g))

    pullback-lift :
      {W X Y Z : Scheme a}
      (f : SchemeHom X Z)
      (g : SchemeHom Y Z)
      (u : SchemeHom W X)
      (v : SchemeHom W Y) →
      HomEquality (compose f u) (compose g v) →
      SchemeHom W (pullback-object f g)

    pullback-lift-left :
      {W X Y Z : Scheme a}
      (f : SchemeHom X Z)
      (g : SchemeHom Y Z)
      (u : SchemeHom W X)
      (v : SchemeHom W Y)
      (commutes : HomEquality (compose f u) (compose g v)) →
      HomEquality
        (compose (pullback-left f g)
                 (pullback-lift f g u v commutes))
        u

    pullback-lift-right :
      {W X Y Z : Scheme a}
      (f : SchemeHom X Z)
      (g : SchemeHom Y Z)
      (u : SchemeHom W X)
      (v : SchemeHom W Y)
      (commutes : HomEquality (compose f u) (compose g v)) →
      HomEquality
        (compose (pullback-right f g)
                 (pullback-lift f g u v commutes))
        v

    pullback-unique :
      {W X Y Z : Scheme a}
      (f : SchemeHom X Z)
      (g : SchemeHom Y Z)
      (u : SchemeHom W X)
      (v : SchemeHom W Y)
      (commutes : HomEquality (compose f u) (compose g v))
      (h : SchemeHom W (pullback-object f g)) →
      HomEquality (compose (pullback-left f g) h) u →
      HomEquality (compose (pullback-right f g) h) v →
      HomEquality h (pullback-lift f g u v commutes)

    diagonal :
      {X Y : Scheme a}
      (f : SchemeHom X Y) →
      SchemeHom X (pullback-object f f)

    diagonal-left :
      {X Y : Scheme a} (f : SchemeHom X Y) →
      HomEquality
        (compose (pullback-left f f) (diagonal f))
        (identity X)

    diagonal-right :
      {X Y : Scheme a} (f : SchemeHom X Y) →
      HomEquality
        (compose (pullback-right f f) (diagonal f))
        (identity X)

    open-subscheme :
      (X : Scheme a) (U : OpenSubset (space X)) →
      OpenSubschemeResult X U

    open-subscheme-compare :
      (X : Scheme a)
      (U : OpenSubset (space X))
      (A B : OpenSubschemeResult X U) →
      SchemeHom
        (OpenSubschemeResult.object A)
        (OpenSubschemeResult.object B)

    open-subscheme-compare-over :
      (X : Scheme a)
      (U : OpenSubset (space X))
      (A B : OpenSubschemeResult X U) →
      HomEquality
        (compose
          (OpenSubschemeResult.inclusion B)
          (open-subscheme-compare X U A B))
        (OpenSubschemeResult.inclusion A)

    open-subscheme-compare-left-inverse :
      (X : Scheme a)
      (U : OpenSubset (space X))
      (A B : OpenSubschemeResult X U) →
      HomEquality
        (compose
          (open-subscheme-compare X U B A)
          (open-subscheme-compare X U A B))
        (identity (OpenSubschemeResult.object A))

    open-subscheme-compare-right-inverse :
      (X : Scheme a)
      (U : OpenSubset (space X))
      (A B : OpenSubschemeResult X U) →
      HomEquality
        (compose
          (open-subscheme-compare X U A B)
          (open-subscheme-compare X U B A))
        (identity (OpenSubschemeResult.object B))

    open-subscheme-compare-unique :
      (X : Scheme a)
      (U : OpenSubset (space X))
      (A B : OpenSubschemeResult X U)
      (h : SchemeHom
        (OpenSubschemeResult.object A)
        (OpenSubschemeResult.object B)) →
      HomEquality
        (compose (OpenSubschemeResult.inclusion B) h)
        (OpenSubschemeResult.inclusion A) →
      HomEquality h (open-subscheme-compare X U A B)

    restriction-source-open :
      {X Y : Scheme a}
      (f : SchemeHom X Y)
      (V : OpenSubset (space Y)) →
      OpenSubschemePresentation
        X
        (inverseOpen f V)
        (pullback-object f
          (OpenSubschemeResult.inclusion (open-subscheme Y V)))
        (pullback-left f
          (OpenSubschemeResult.inclusion (open-subscheme Y V)))

    restriction-source-compare :
      {X Y : Scheme a}
      (f : SchemeHom X Y)
      (V : OpenSubset (space Y))
      (A B : OpenSubschemeResult Y V) →
      SchemeHom
        (pullback-object f (OpenSubschemeResult.inclusion A))
        (pullback-object f (OpenSubschemeResult.inclusion B))

    restriction-source-compare-over-source :
      {X Y : Scheme a}
      (f : SchemeHom X Y)
      (V : OpenSubset (space Y))
      (A B : OpenSubschemeResult Y V) →
      HomEquality
        (compose
          (pullback-left f (OpenSubschemeResult.inclusion B))
          (restriction-source-compare f V A B))
        (pullback-left f (OpenSubschemeResult.inclusion A))

    restriction-arrows-compatible :
      {X Y : Scheme a}
      (f : SchemeHom X Y)
      (V : OpenSubset (space Y))
      (A B : OpenSubschemeResult Y V) →
      HomEquality
        (compose
          (pullback-right f (OpenSubschemeResult.inclusion B))
          (restriction-source-compare f V A B))
        (compose
          (open-subscheme-compare Y V A B)
          (pullback-right f (OpenSubschemeResult.inclusion A)))

    restriction-source-compare-left-inverse :
      {X Y : Scheme a}
      (f : SchemeHom X Y)
      (V : OpenSubset (space Y))
      (A B : OpenSubschemeResult Y V) →
      HomEquality
        (compose
          (restriction-source-compare f V B A)
          (restriction-source-compare f V A B))
        (identity
          (pullback-object f (OpenSubschemeResult.inclusion A)))

    restriction-source-compare-right-inverse :
      {X Y : Scheme a}
      (f : SchemeHom X Y)
      (V : OpenSubset (space Y))
      (A B : OpenSubschemeResult Y V) →
      HomEquality
        (compose
          (restriction-source-compare f V A B)
          (restriction-source-compare f V B A))
        (identity
          (pullback-object f (OpenSubschemeResult.inclusion B)))

    restriction-source-compare-unique :
      {X Y : Scheme a}
      (f : SchemeHom X Y)
      (V : OpenSubset (space Y))
      (A B : OpenSubschemeResult Y V)
      (h : SchemeHom
        (pullback-object f (OpenSubschemeResult.inclusion A))
        (pullback-object f (OpenSubschemeResult.inclusion B))) →
      HomEquality
        (compose
          (pullback-left f (OpenSubschemeResult.inclusion B)) h)
        (pullback-left f (OpenSubschemeResult.inclusion A)) →
      HomEquality
        (compose
          (pullback-right f (OpenSubschemeResult.inclusion B)) h)
        (compose
          (open-subscheme-compare Y V A B)
          (pullback-right f (OpenSubschemeResult.inclusion A))) →
      HomEquality h (restriction-source-compare f V A B)

open SchemeCategory

restrictionTarget : ∀ {a} (C : SchemeCategory a)
                    {Y : Scheme a} →
                    OpenSubset (space Y) → Scheme a
restrictionTarget C {Y = Y} V =
  OpenSubschemeResult.object (open-subscheme C Y V)

restrictionInclusion : ∀ {a} (C : SchemeCategory a)
                       {Y : Scheme a}
                       (V : OpenSubset (space Y)) →
                       SchemeHom (restrictionTarget C V) Y
restrictionInclusion C {Y = Y} V =
  OpenSubschemeResult.inclusion (open-subscheme C Y V)

restrictionSource : ∀ {a} (C : SchemeCategory a)
                    {X Y : Scheme a} →
                    SchemeHom X Y →
                    (V : OpenSubset (space Y)) → Scheme a
restrictionSource C f V =
  pullback-object C f (restrictionInclusion C V)

restrictionArrow : ∀ {a} (C : SchemeCategory a)
                   {X Y : Scheme a}
                   (f : SchemeHom X Y)
                   (V : OpenSubset (space Y)) →
                   SchemeHom (restrictionSource C f V)
                             (restrictionTarget C V)
restrictionArrow C f V =
  pullback-right C f (restrictionInclusion C V)

record AffineFiniteTypeNeighborhood {a : Level}
       {X Y : Scheme a}
       (f : SchemeHom X Y)
       (x : Point (space X)) : Setω where
  field
    source-open     : OpenSubset (space X)
    target-open     : OpenSubset (space Y)
    source-contains : x ∈ source-open
    target-contains : on-points f x ∈ target-open
    maps-into       :
      MapsInto {X = X} {Y = Y}
        (on-points f) source-open target-open
    source-affine   :
      AffinePresentation (structureSheaf X) source-open
    target-affine   :
      AffinePresentation (structureSheaf Y) target-open
    finite-type-map :
      FiniteTypeRingHom
        (on-sections f source-open target-open maps-into)

record LocallyOfFiniteType {a : Level}
                           {X Y : Scheme a}
                           (f : SchemeHom X Y) : Setω where
  field
    affine-neighborhoods :
      (x : Point (space X)) →
      AffineFiniteTypeNeighborhood f x

IsSeparated : ∀ {a} (C : SchemeCategory a) {X Y : Scheme a} →
              SchemeHom X Y → Setω
IsSeparated C f = ClosedImmersion (diagonal C f)

UniversallyClosed : ∀ {a} (C : SchemeCategory a) {X Y : Scheme a} →
                    SchemeHom X Y → Setω
UniversallyClosed {a = a} C {Y = Y} f =
  (Y′ : Scheme a) →
  (g : SchemeHom Y′ Y) →
  ClosedMap
    {S = space (pullback-object C f g)}
    {T = space Y′}
    (on-points
      (pullback-right C f g))

record IsProper {a : Level}
                {X Y : Scheme a}
                (f : SchemeHom X Y) : Setω where
  field
    category            : SchemeCategory a
    locally-finite-type : LocallyOfFiniteType f
    separated           : IsSeparated category f
    universally-closed  : UniversallyClosed category f

record IsFinite {a : Level}
                {X Y : Scheme a}
                (f : SchemeHom X Y) : Setω where
  field
    affine-preimages :
      (V : OpenSubset (space Y)) →
      AffinePresentation (structureSheaf Y) V →
      AffinePresentation (structureSheaf X) (inverseOpen f V)

    finite-on-coordinate-rings :
      (V : OpenSubset (space Y))
      (affineV : AffinePresentation (structureSheaf Y) V) →
      FiniteRingHom
        (on-sections f (inverseOpen f V) V
          (inverseMapsInto f V))

Fiber : ∀ {a} {X Y : Scheme a} →
        SchemeHom X Y → Point (space Y) → Set a
Fiber {X = X} f y =
  Σ[ x ∈ Point (space X) ] (on-points f x ≡ y)

record FiniteNeighborhoodConclusion {a : Level}
       {X Y : Scheme a}
       (f : SchemeHom X Y)
       (proper : IsProper f)
       (y : Point (space Y)) : Setω where
  field
    neighborhood : OpenSubset (space Y)
    contains     : y ∈ neighborhood
    finite       :
      IsFinite
        (restrictionArrow
          (IsProper.category proper)
          f
          neighborhood)

ZariskiMainTheoremStatement : Setω
ZariskiMainTheoremStatement =
  {a : Level} →
  {X Y : Scheme a} →
  (f : SchemeHom X Y) →
  (proper : IsProper f) →
  (y : Point (space Y)) →
  Finite (Fiber f y) →
  FiniteNeighborhoodConclusion f proper y
