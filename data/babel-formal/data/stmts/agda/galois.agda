-- Statement-only formalization of the Babel-formal topic galois. This file contains no proof.

module galois where

open import Agda.Builtin.Equality using (_≡_)

data ⊥ : Set where

infix 4 _≢_
_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

infixr 2 _∧_
record _∧_ (A B : Set) : Set where
  field
    left  : A
    right : B

record Field (F : Set) : Set where
  field
    zero     : F
    one      : F
    add      : F → F → F
    multiply : F → F → F
    negate   : F → F
    inverse  : F → F

    add-commutative : (x y : F) → add x y ≡ add y x
    add-associative :
      (x y z : F) → add (add x y) z ≡ add x (add y z)
    add-zero : (x : F) → add x zero ≡ x
    add-inverse-left : (x : F) → add (negate x) x ≡ zero

    multiply-commutative :
      (x y : F) → multiply x y ≡ multiply y x
    multiply-associative :
      (x y z : F) →
      multiply (multiply x y) z ≡ multiply x (multiply y z)
    multiply-one-left : (x : F) → multiply one x ≡ x
    multiply-inverse-left :
      (x : F) → x ≢ zero → multiply (inverse x) x ≡ one

    distribute-left :
      (x y z : F) →
      multiply x (add y z) ≡ add (multiply x y) (multiply x z)

    zero-not-one    : zero ≢ one
    inverse-nonzero : (x : F) → x ≢ zero → inverse x ≢ zero

module FieldProperties {F : Set} (structure : Field F) where
  open Field structure

  add-cancel-left : Set
  add-cancel-left =
    (x y z : F) → add x y ≡ add x z → y ≡ z

  add-cancel-right : Set
  add-cancel-right =
    (x y z : F) → add y x ≡ add z x → y ≡ z

  multiply-cancel-left : Set
  multiply-cancel-left =
    (x y z : F) →
    x ≢ zero →
    multiply x y ≡ multiply x z →
    y ≡ z

  multiply-cancel-right : Set
  multiply-cancel-right =
    (x y z : F) →
    x ≢ zero →
    multiply y x ≡ multiply z x →
    y ≡ z

  inverse-unique : Set
  inverse-unique =
    (x y : F) →
    x ≢ zero →
    multiply x y ≡ one →
    y ≡ inverse x

  inverse-involutive : Set
  inverse-involutive =
    (x : F) → x ≢ zero → inverse (inverse x) ≡ x

module Tower
  (Polynomial : Set → Set)
  (SplittingField : {F : Set} → Polynomial F → Set)
  (algebraMap : {F K : Set} → F → K)
  (Splits : {F K : Set} → Polynomial F → (F → K) → Set)
  (mapPolynomial :
    {F K : Set} → Polynomial F → (F → K) → Polynomial K)
  (GaloisGroup : {F : Set} → Polynomial F → Set)
  (IsSolvable : Set → Set)
  where

  record TowerAxioms : Set₁ where
    field
      map-polynomial-compose :
        {F K L : Set} →
        (p : Polynomial F) →
        (f : F → K) →
        (g : K → L) →
        mapPolynomial (mapPolynomial p f) g ≡
        mapPolynomial p (λ x → g (f x))

      is-solvable-of-scalar-tower :
        {F K : Set} {p q : Polynomial F} →
        IsSolvable (GaloisGroup p) →
        IsSolvable
          (GaloisGroup
            (mapPolynomial q (algebraMap {F = F} {K = K}))) →
        IsSolvable (GaloisGroup q)

      is-solvable-map-polynomial :
        {F K : Set} →
        (p : Polynomial F) →
        IsSolvable (GaloisGroup p) →
        IsSolvable
          (GaloisGroup
            (mapPolynomial p (algebraMap {F = F} {K = K})))

      is-solvable-of-splits :
        {F K : Set} →
        (p : Polynomial F) →
        (f : F → K) →
        Splits p f →
        IsSolvable (GaloisGroup p)

  gal-isSolvable-tower :
    {F : Set} → (p q : Polynomial F) → Set₁
  gal-isSolvable-tower {F} p q =
    TowerAxioms →
    IsSolvable (GaloisGroup p) →
    IsSolvable
      (GaloisGroup
        (mapPolynomial q
          (algebraMap {F = F} {K = SplittingField p}))) →
    IsSolvable (GaloisGroup q)

  gal-isSolvable-double-tower :
    {F : Set} → (p q r : Polynomial F) → Set₁
  gal-isSolvable-double-tower {F} p q r =
    TowerAxioms →
    IsSolvable (GaloisGroup p) →
    IsSolvable
      (GaloisGroup
        (mapPolynomial q
          (algebraMap {F = F} {K = SplittingField p}))) →
    IsSolvable
      (GaloisGroup
        (mapPolynomial r
          (algebraMap {F = F} {K = SplittingField q}))) →
    IsSolvable (GaloisGroup r)

  gal-isSolvable-triple-tower :
    {F : Set} → (p q r s : Polynomial F) → Set₁
  gal-isSolvable-triple-tower {F} p q r s =
    TowerAxioms →
    IsSolvable (GaloisGroup p) →
    IsSolvable
      (GaloisGroup
        (mapPolynomial q
          (algebraMap {F = F} {K = SplittingField p}))) →
    IsSolvable
      (GaloisGroup
        (mapPolynomial r
          (algebraMap {F = F} {K = SplittingField q}))) →
    IsSolvable
      (GaloisGroup
        (mapPolynomial s
          (algebraMap {F = F} {K = SplittingField r}))) →
    IsSolvable (GaloisGroup s)

  gal-isSolvable-quadruple-tower :
    {F : Set} → (p q r s t : Polynomial F) → Set₁
  gal-isSolvable-quadruple-tower {F} p q r s t =
    TowerAxioms →
    IsSolvable (GaloisGroup p) →
    IsSolvable
      (GaloisGroup
        (mapPolynomial q
          (algebraMap {F = F} {K = SplittingField p}))) →
    IsSolvable
      (GaloisGroup
        (mapPolynomial r
          (algebraMap {F = F} {K = SplittingField q}))) →
    IsSolvable
      (GaloisGroup
        (mapPolynomial s
          (algebraMap {F = F} {K = SplittingField r}))) →
    IsSolvable
      (GaloisGroup
        (mapPolynomial t
          (algebraMap {F = F} {K = SplittingField s}))) →
    IsSolvable (GaloisGroup t)

  gal-isSolvable-map-polynomial :
    {F : Set} → (p : Polynomial F) → (K : Set) → Set₁
  gal-isSolvable-map-polynomial {F} p K =
    TowerAxioms →
    IsSolvable (GaloisGroup p) →
    IsSolvable
      (GaloisGroup
        (mapPolynomial p (algebraMap {F = F} {K = K})))

  gal-isSolvable-of-split :
    {F : Set} → (p : Polynomial F) → Set₁
  gal-isSolvable-of-split {F} p =
    TowerAxioms →
    Splits p (algebraMap {F = F} {K = SplittingField p}) →
    IsSolvable (GaloisGroup p)

  gal-isSolvable-split-tower :
    {F : Set} → (p q : Polynomial F) → Set₁
  gal-isSolvable-split-tower {F} p q =
    TowerAxioms →
    Splits q (algebraMap {F = F} {K = SplittingField p}) →
    IsSolvable (GaloisGroup q)

  gal-isSolvable-two-step-map :
    {F : Set} → (p : Polynomial F) → (K L : Set) → Set₁
  gal-isSolvable-two-step-map {F} p K L =
    TowerAxioms →
    IsSolvable (GaloisGroup p) →
    IsSolvable
      (GaloisGroup
        (mapPolynomial
          (mapPolynomial p (algebraMap {F = F} {K = K}))
          (algebraMap {F = K} {K = L})))

  gal-isSolvable-three-step-map :
    {F : Set} → (p : Polynomial F) → (K L M : Set) → Set₁
  gal-isSolvable-three-step-map {F} p K L M =
    TowerAxioms →
    IsSolvable (GaloisGroup p) →
    IsSolvable
      (GaloisGroup
        (mapPolynomial
          (mapPolynomial
            (mapPolynomial p (algebraMap {F = F} {K = K}))
            (algebraMap {F = K} {K = L}))
          (algebraMap {F = L} {K = M})))

  gal-isSolvable-map-polynomial-compose :
    {F : Set} → (p : Polynomial F) → (K L : Set) → Set₁
  gal-isSolvable-map-polynomial-compose {F} p K L =
    TowerAxioms →
    IsSolvable (GaloisGroup p) →
    IsSolvable
      (GaloisGroup
        (mapPolynomial
          (mapPolynomial p (algebraMap {F = F} {K = K}))
          (algebraMap {F = K} {K = L})))

  gal-isSolvable-mutual-split :
    {F : Set} → (p q : Polynomial F) → Set₁
  gal-isSolvable-mutual-split {F} p q =
    TowerAxioms →
    Splits p (algebraMap {F = F} {K = SplittingField q}) →
    Splits q (algebraMap {F = F} {K = SplittingField p}) →
    IsSolvable (GaloisGroup p) ∧ IsSolvable (GaloisGroup q)

  gal-isSolvable-tower-split :
    {F : Set} → (p q r : Polynomial F) → Set₁
  gal-isSolvable-tower-split {F} p q r =
    TowerAxioms →
    Splits q (algebraMap {F = F} {K = SplittingField p}) →
    IsSolvable
      (GaloisGroup
        (mapPolynomial r
          (algebraMap {F = F} {K = SplittingField q}))) →
    IsSolvable (GaloisGroup r)

  gal-isSolvable-map-after-split :
    {F : Set} → (p : Polynomial F) → (K : Set) → Set₁
  gal-isSolvable-map-after-split {F} p K =
    TowerAxioms →
    Splits p (algebraMap {F = F} {K = SplittingField p}) →
    IsSolvable
      (GaloisGroup
        (mapPolynomial p (algebraMap {F = F} {K = K})))
