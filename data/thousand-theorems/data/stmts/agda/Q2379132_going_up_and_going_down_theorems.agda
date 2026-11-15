-- Statement-only formalization of thousand-theorems corpus artifact Q2379132,
-- "Going-up and going-down theorems". It states the two indexed going-up
-- results, the prime-spectrum characterization of going-down, and the
-- localized-spectrum surjectivity criterion. This file contains no proof.

{-# OPTIONS --safe #-}

module Q2379132_going_up_and_going_down_theorems where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ)

infixr 3 _and_
infixr 2 _or_

data Bottom {a : Level} : Set a where

Not :
  {a : Level} →
  Set a →
  Set a
Not {a} A =
  A → Bottom {a}

record _and_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

data _or_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  left  : A → A or B
  right : B → A or B

record Iff
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor equivalence
  field
    forward  : A → B
    backward : B → A

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (suc n)
  fsuc  : {n : Nat} → Fin n → Fin (suc n)

finToNat :
  {n : Nat} →
  Fin n →
  Nat
finToNat fzero =
  zero
finToNat (fsuc i) =
  suc (finToNat i)

last :
  (n : Nat) →
  Fin (suc n)
last zero =
  fzero
last (suc n) =
  fsuc (last n)

record CommutativeRing
  {r : Level}
  (R : Set r) :
  Set r where

  field
    zeroR oneR : R
    addR multiplyR : R → R → R
    negateR : R → R

    add-associative :
      (x y z : R) →
      addR (addR x y) z ≡ addR x (addR y z)
    add-commutative :
      (x y : R) →
      addR x y ≡ addR y x
    add-zero-left :
      (x : R) →
      addR zeroR x ≡ x
    add-zero-right :
      (x : R) →
      addR x zeroR ≡ x
    add-inverse-left :
      (x : R) →
      addR (negateR x) x ≡ zeroR
    add-inverse-right :
      (x : R) →
      addR x (negateR x) ≡ zeroR

    multiply-associative :
      (x y z : R) →
      multiplyR (multiplyR x y) z ≡
      multiplyR x (multiplyR y z)
    multiply-commutative :
      (x y : R) →
      multiplyR x y ≡ multiplyR y x
    multiply-one-left :
      (x : R) →
      multiplyR oneR x ≡ x
    multiply-one-right :
      (x : R) →
      multiplyR x oneR ≡ x
    distribute-left :
      (x y z : R) →
      multiplyR x (addR y z) ≡
      addR (multiplyR x y) (multiplyR x z)
    distribute-right :
      (x y z : R) →
      multiplyR (addR x y) z ≡
      addR (multiplyR x z) (multiplyR y z)

record RingHom
  {r s : Level}
  {R : Set r}
  {S : Set s}
  (domain : CommutativeRing R)
  (codomain : CommutativeRing S) :
  Set (r ⊔ s) where

  field
    map : R → S
    map-zero :
      map (CommutativeRing.zeroR domain) ≡
      CommutativeRing.zeroR codomain
    map-one :
      map (CommutativeRing.oneR domain) ≡
      CommutativeRing.oneR codomain
    map-add :
      (x y : R) →
      map (CommutativeRing.addR domain x y) ≡
      CommutativeRing.addR codomain (map x) (map y)
    map-multiply :
      (x y : R) →
      map (CommutativeRing.multiplyR domain x y) ≡
      CommutativeRing.multiplyR codomain (map x) (map y)

record Ideal
  {r : Level}
  {R : Set r}
  (ring : CommutativeRing R) :
  Set (lsuc r) where

  field
    member : R → Set r
    membership-propositional :
      (x : R) →
      (u v : member x) →
      u ≡ v
    contains-zero :
      member (CommutativeRing.zeroR ring)
    closed-under-addition :
      (x y : R) →
      member x →
      member y →
      member (CommutativeRing.addR ring x y)
    closed-under-negation :
      (x : R) →
      member x →
      member (CommutativeRing.negateR ring x)
    absorbs-multiplication :
      (a x : R) →
      member x →
      member (CommutativeRing.multiplyR ring a x)

IsPrime :
  {r : Level} →
  {R : Set r} →
  {ring : CommutativeRing R} →
  Ideal ring →
  Set r
IsPrime {R = R} {ring = ring} ideal =
  Not (Ideal.member ideal (CommutativeRing.oneR ring)) and
  ((x y : R) →
    Ideal.member ideal (CommutativeRing.multiplyR ring x y) →
    Ideal.member ideal x or Ideal.member ideal y)

IsDomain :
  {r : Level} →
  {R : Set r} →
  CommutativeRing R →
  Set r
IsDomain {R = R} ring =
  Not
    (CommutativeRing.oneR ring ≡
     CommutativeRing.zeroR ring)
  and
  ((x y : R) →
    CommutativeRing.multiplyR ring x y ≡
    CommutativeRing.zeroR ring →
    (x ≡ CommutativeRing.zeroR ring) or
    (y ≡ CommutativeRing.zeroR ring))

power :
  {r : Level} →
  {R : Set r} →
  CommutativeRing R →
  R →
  Nat →
  R
power ring x zero =
  CommutativeRing.oneR ring
power ring x (suc n) =
  CommutativeRing.multiplyR ring x (power ring x n)

sumFin :
  {r : Level} →
  {R : Set r} →
  CommutativeRing R →
  (n : Nat) →
  (Fin n → R) →
  R
sumFin ring zero values =
  CommutativeRing.zeroR ring
sumFin ring (suc n) values =
  CommutativeRing.addR ring
    (values fzero)
    (sumFin ring n (λ i → values (fsuc i)))

evaluatePolynomial :
  {r s : Level} →
  {R : Set r} →
  {S : Set s} →
  (domain : CommutativeRing R) →
  (codomain : CommutativeRing S) →
  RingHom domain codomain →
  (n : Nat) →
  (Fin (suc n) → R) →
  S →
  S
evaluatePolynomial domain codomain hom n coefficients x =
  sumFin codomain (suc n)
    (λ i →
      CommutativeRing.multiplyR codomain
        (RingHom.map hom (coefficients i))
        (power codomain x (finToNat i)))

IsIntegral :
  {r s : Level} →
  {R : Set r} →
  {S : Set s} →
  (domain : CommutativeRing R) →
  (codomain : CommutativeRing S) →
  RingHom domain codomain →
  Set (r ⊔ s)
IsIntegral {R = R} {S = S} domain codomain hom =
  (x : S) →
  Σ Nat
    (λ degree →
      Σ (Fin (suc degree) → R)
        (λ coefficients →
          (coefficients (last degree) ≡
           CommutativeRing.oneR domain)
          and
          (evaluatePolynomial
             domain codomain hom degree coefficients x
           ≡
           CommutativeRing.zeroR codomain)))

KernelContainedIn :
  {r s : Level} →
  {R : Set r} →
  {S : Set s} →
  {domain : CommutativeRing R} →
  {codomain : CommutativeRing S} →
  RingHom domain codomain →
  Ideal domain →
  Set (r ⊔ s)
KernelContainedIn {R = R} {codomain = codomain} hom ideal =
  (x : R) →
  RingHom.map hom x ≡ CommutativeRing.zeroR codomain →
  Ideal.member ideal x

ContractionEqual :
  {r s : Level} →
  {R : Set r} →
  {S : Set s} →
  {domain : CommutativeRing R} →
  {codomain : CommutativeRing S} →
  RingHom domain codomain →
  Ideal codomain →
  Ideal domain →
  Set (r ⊔ s)
ContractionEqual {R = R} hom upstairs downstairs =
  (x : R) →
  Iff
    (Ideal.member upstairs (RingHom.map hom x))
    (Ideal.member downstairs x)

IdealIncluded :
  {r : Level} →
  {R : Set r} →
  {ring : CommutativeRing R} →
  Ideal ring →
  Ideal ring →
  Set r
IdealIncluded {R = R} smaller larger =
  (x : R) →
  Ideal.member smaller x →
  Ideal.member larger x

ContractionIncludedInIdeal :
  {r s : Level} →
  {R : Set r} →
  {S : Set s} →
  {domain : CommutativeRing R} →
  {codomain : CommutativeRing S} →
  RingHom domain codomain →
  Ideal codomain →
  Ideal domain →
  Set (r ⊔ s)
ContractionIncludedInIdeal {R = R} hom upstairs downstairs =
  (x : R) →
  Ideal.member upstairs (RingHom.map hom x) →
  Ideal.member downstairs x

IdealBelowContraction :
  {r s : Level} →
  {R : Set r} →
  {S : Set s} →
  {domain : CommutativeRing R} →
  {codomain : CommutativeRing S} →
  RingHom domain codomain →
  Ideal domain →
  Ideal codomain →
  Set (r ⊔ s)
IdealBelowContraction {R = R} hom downstairs upstairs =
  (x : R) →
  Ideal.member downstairs x →
  Ideal.member upstairs (RingHom.map hom x)

HasGoingDown :
  {r s : Level} →
  {R : Set r} →
  {S : Set s} →
  (domain : CommutativeRing R) →
  (codomain : CommutativeRing S) →
  RingHom domain codomain →
  Set (lsuc (r ⊔ s))
HasGoingDown domain codomain hom =
  (p q : Ideal domain) →
  IsPrime p →
  IsPrime q →
  IdealIncluded p q →
  (Q : Ideal codomain) →
  IsPrime Q →
  ContractionEqual hom Q q →
  Σ (Ideal codomain)
    (λ P →
      IsPrime P and
      (IdealIncluded P Q and
       ContractionEqual hom P p))

GeneralizingPrimeSpectrumComap :
  {r s : Level} →
  {R : Set r} →
  {S : Set s} →
  (domain : CommutativeRing R) →
  (codomain : CommutativeRing S) →
  RingHom domain codomain →
  Set (lsuc (r ⊔ s))
GeneralizingPrimeSpectrumComap domain codomain hom =
  (Q : Ideal codomain) →
  IsPrime Q →
  (p : Ideal domain) →
  IsPrime p →
  IdealBelowContraction hom p Q →
  Σ (Ideal codomain)
    (λ P →
      IsPrime P and
      (IdealIncluded P Q and
       ContractionEqual hom P p))

LocalPrimeSpectrumComapSurjective :
  {r s : Level} →
  {R : Set r} →
  {S : Set s} →
  (domain : CommutativeRing R) →
  (codomain : CommutativeRing S) →
  RingHom domain codomain →
  Ideal codomain →
  Set (lsuc (r ⊔ s))
LocalPrimeSpectrumComapSurjective domain codomain hom Q =
  (p : Ideal domain) →
  IsPrime p →
  IdealBelowContraction hom p Q →
  Σ (Ideal codomain)
    (λ P →
      IsPrime P and
      (IdealIncluded P Q and
       ContractionEqual hom P p))

-- Lean: Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain
going-up-and-going-down-theorems :
  (r s : Level) →
  Set (lsuc (r ⊔ s))
going-up-and-going-down-theorems r s =
  (R : Set r) →
  (S : Set s) →
  (domain : CommutativeRing R) →
  (codomain : CommutativeRing S) →
  (algebra-map : RingHom domain codomain) →
  IsDomain codomain →
  IsIntegral domain codomain algebra-map →
  (P : Ideal domain) →
  IsPrime P →
  KernelContainedIn algebra-map P →
  Σ (Ideal codomain)
    (λ Q →
      IsPrime Q and
      ContractionEqual algebra-map Q P)

-- Lean: Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime
general-going-up-above-prime :
  (r s : Level) →
  Set (lsuc (r ⊔ s))
general-going-up-above-prime r s =
  (R : Set r) →
  (S : Set s) →
  (domain : CommutativeRing R) →
  (codomain : CommutativeRing S) →
  (algebra-map : RingHom domain codomain) →
  IsIntegral domain codomain algebra-map →
  (P : Ideal domain) →
  IsPrime P →
  (I : Ideal codomain) →
  IsPrime I →
  ContractionIncludedInIdeal algebra-map I P →
  Σ (Ideal codomain)
    (λ Q →
      IdealIncluded I Q and
      (IsPrime Q and
       ContractionEqual algebra-map Q P))

-- Lean: Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap
going-down-iff-generalizing-prime-spectrum-comap :
  (r s : Level) →
  Set (lsuc (r ⊔ s))
going-down-iff-generalizing-prime-spectrum-comap r s =
  (R : Set r) →
  (S : Set s) →
  (domain : CommutativeRing R) →
  (codomain : CommutativeRing S) →
  (algebra-map : RingHom domain codomain) →
  Iff
    (HasGoingDown domain codomain algebra-map)
    (GeneralizingPrimeSpectrumComap domain codomain algebra-map)

-- Lean: Algebra.HasGoingDown.of_comap_localRingHom_surjective
going-down-from-local-prime-spectrum-surjectivity :
  (r s : Level) →
  Set (lsuc (r ⊔ s))
going-down-from-local-prime-spectrum-surjectivity r s =
  (R : Set r) →
  (S : Set s) →
  (domain : CommutativeRing R) →
  (codomain : CommutativeRing S) →
  (algebra-map : RingHom domain codomain) →
  ((Q : Ideal codomain) →
    IsPrime Q →
    LocalPrimeSpectrumComapSurjective
      domain codomain algebra-map Q) →
  HasGoingDown domain codomain algebra-map
