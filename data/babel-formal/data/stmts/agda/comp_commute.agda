-- Statement-only formalization of the Babel-formal topic comp_commute. This file contains no
-- proof.

module comp_commute where

open import Agda.Primitive using (Level; Setω)
open import Agda.Builtin.Equality using (_≡_)

comp : ∀ {a b c : Level}
         {A : Set a} {B : Set b} {C : Set c} →
       (B → C) → (A → B) → A → C
comp g f x = g (f x)

id : ∀ {a : Level} {A : Set a} → A → A
id x = x

record FunProps : Setω where
  field
    comp-assoc :
      ∀ {a b c d : Level}
        {A : Set a} {B : Set b} {C : Set c} {D : Set d}
        (h : C → D) (g : B → C) (f : A → B) →
        comp h (comp g f) ≡ comp (comp h g) f

    comp-id-l :
      ∀ {a b : Level} {A : Set a} {B : Set b}
        (f : A → B) →
        comp id f ≡ f

    comp-id-r :
      ∀ {a b : Level} {A : Set a} {B : Set b}
        (f : A → B) →
        comp f id ≡ f

commute : ∀ {a : Level} {A : Set a} → (A → A) → (A → A) → Set a
commute f g = comp f g ≡ comp g f

module CompCommute {a : Level} {A : Set a} (FP : FunProps) where
  open FunProps FP

  commute-symm : Set a
  commute-symm =
    (f g : A → A) →
    commute f g →
    commute g f

  commute-with-id-l : Set a
  commute-with-id-l =
    (f : A → A) →
    commute f id

  commute-with-id-r : Set a
  commute-with-id-r =
    (f : A → A) →
    commute id f

  commute-refl : Set a
  commute-refl =
    (f : A → A) →
    commute f f

  commute-congr : Set a
  commute-congr =
    (f1 f2 g1 g2 : A → A) →
    f1 ≡ f2 →
    g1 ≡ g2 →
    commute f1 g1 →
    commute f2 g2

  commute-transport-left-id : Set a
  commute-transport-left-id =
    (f g : A → A) →
    commute f g →
    commute (comp id f) g

  commute-transport-right-id : Set a
  commute-transport-right-id =
    (f g : A → A) →
    commute f g →
    commute f (comp id g)
