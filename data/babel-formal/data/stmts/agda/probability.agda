-- Statement-only formalization of the Babel-formal artifact probability: event algebra,
-- conditional probability, independence, disjoint finite unions, and inclusion-exclusion over
-- a generic ring-valued probability context. This file contains no proof.

module probability where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_)

data ⊥ {ℓ : Level} : Set ℓ where

record ⊤ {ℓ : Level} : Set ℓ where
  constructor tt

infixr 4 _∧_
record _∧_ {ℓ₁ ℓ₂ : Level}
           (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor _,_
  field
    and-left  : A
    and-right : B

infixr 3 _∨_
data _∨_ {ℓ₁ ℓ₂ : Level}
         (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  or-left  : A → A ∨ B
  or-right : B → A ∨ B

infix 8 ¬_
¬_ : {ℓ : Level} → Set ℓ → Set ℓ
¬_ {ℓ} A = A → ⊥ {ℓ}

infix 2 _↔_
record _↔_ {ℓ₁ ℓ₂ : Level}
           (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  field
    iff-forward  : A → B
    iff-backward : B → A

infix 4 _≢_
_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

data MyNat : Set where
  O : MyNat
  S : MyNat → MyNat

mynat-add : MyNat → MyNat → MyNat
mynat-add O       m = m
mynat-add (S n)   m = S (mynat-add n m)

mynat-add-O-left : Set
mynat-add-O-left =
  (m : MyNat) → mynat-add O m ≡ m

mynat-add-S-left : Set
mynat-add-S-left =
  (n m : MyNat) → mynat-add (S n) m ≡ S (mynat-add n m)

infixr 5 _∷L_
data MyList {ℓ : Level} (A : Set ℓ) : Set ℓ where
  nilL : MyList A
  _∷L_ : A → MyList A → MyList A

infix 4 _∈L_
data _∈L_ {ℓ : Level} {A : Set ℓ}
            (x : A) : MyList A → Set ℓ where
  in-head : {xs : MyList A} → x ∈L (x ∷L xs)
  in-tail : {y : A} {xs : MyList A} →
            x ∈L xs → x ∈L (y ∷L xs)

data NoDupL {ℓ : Level} {A : Set ℓ} : MyList A → Set ℓ where
  nd-nil  : NoDupL nilL
  nd-cons : {x : A} {xs : MyList A} →
            ¬ (x ∈L xs) → NoDupL xs → NoDupL (x ∷L xs)

mapL : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {B : Set ℓ₂} →
       (A → B) → MyList A → MyList B
mapL f nilL       = nilL
mapL f (x ∷L xs)  = f x ∷L mapL f xs

fold-add : {ℓ : Level} {A : Set ℓ} →
           (A → A → A) → A → MyList A → A
fold-add add zero nilL       = zero
fold-add add zero (x ∷L xs)  = add x (fold-add add zero xs)

Event : Set → Set₁
Event Ω = Ω → Set

ev-false : {Ω : Set} → Event Ω
ev-false _ = ⊥

ev-true : {Ω : Set} → Event Ω
ev-true _ = ⊤

ev-inter : {Ω : Set} → Event Ω → Event Ω → Event Ω
ev-inter A B ω = A ω ∧ B ω

ev-union : {Ω : Set} → Event Ω → Event Ω → Event Ω
ev-union A B ω = A ω ∨ B ω

ev-compl : {Ω : Set} → Event Ω → Event Ω
ev-compl A ω = ¬ (A ω)

ev-diff : {Ω : Set} → Event Ω → Event Ω → Event Ω
ev-diff A B ω = A ω ∧ ¬ (B ω)

Disjoint : {Ω : Set} → Event Ω → Event Ω → Set
Disjoint {Ω} A B =
  (ω : Ω) → ¬ (ev-inter A B ω)

PairwiseDisjoint :
  {Ω : Set} → MyList (Event Ω) → Set₁
PairwiseDisjoint nilL = ⊤
PairwiseDisjoint (A ∷L nilL) = ⊤
PairwiseDisjoint {Ω} (A ∷L (B ∷L xs)) =
  Disjoint A B ∧
  (((C : Event Ω) → C ∈L (B ∷L xs) → Disjoint A C) ∧
   PairwiseDisjoint (B ∷L xs))

bigUnion : {Ω : Set} → MyList (Event Ω) → Event Ω
bigUnion nilL       = ev-false
bigUnion (A ∷L xs)  = ev-union A (bigUnion xs)

module EventStatements {Ω : Set} where

  ev-inter-comm : Set₁
  ev-inter-comm =
    (A B : Event Ω) → (ω : Ω) →
    ev-inter A B ω ↔ ev-inter B A ω

  ev-union-comm : Set₁
  ev-union-comm =
    (A B : Event Ω) → (ω : Ω) →
    ev-union A B ω ↔ ev-union B A ω

  ev-inter-assoc : Set₁
  ev-inter-assoc =
    (A B C : Event Ω) → (ω : Ω) →
    ev-inter (ev-inter A B) C ω ↔
    ev-inter A (ev-inter B C) ω

  ev-union-assoc : Set₁
  ev-union-assoc =
    (A B C : Event Ω) → (ω : Ω) →
    ev-union (ev-union A B) C ω ↔
    ev-union A (ev-union B C) ω

  ev-inter-distrib-left : Set₁
  ev-inter-distrib-left =
    (A B C : Event Ω) → (ω : Ω) →
    ev-inter A (ev-union B C) ω ↔
    ev-union (ev-inter A B) (ev-inter A C) ω

record Ring (R : Set) : Set where
  field
    zero : R
    opp  : R → R
    one  : R
    add  : R → R → R
    mul  : R → R → R

    one-neq-zero : one ≢ zero

    add-comm  : (x y : R) → add x y ≡ add y x
    add-assoc : (x y z : R) →
                add (add x y) z ≡ add x (add y z)
    add-zero  : (x : R) → add x zero ≡ x
    add-opp   : (x : R) → add x (opp x) ≡ zero

    mul-comm  : (x y : R) → mul x y ≡ mul y x
    mul-assoc : (x y z : R) →
                mul (mul x y) z ≡ mul x (mul y z)
    mul-one   : (x : R) → mul x one ≡ x
    dist-left : (x y z : R) →
                mul x (add y z) ≡ add (mul x y) (mul x z)
    mul-zero  : (x : R) → mul x zero ≡ zero

    no-zero-div :
      (x y : R) →
      mul x y ≡ zero →
      (x ≡ zero) ∨ (y ≡ zero)

Indep :
  {R Ω : Set} →
  Ring R →
  (Event Ω → R) →
  Event Ω → Event Ω → Set
Indep ring prob A B =
  prob (ev-inter A B) ≡
  Ring.mul ring (prob A) (prob B)

record ProbabilityContext
  (R Ω : Set) (ring : Ring R) : Set₁ where

  open Ring ring

  field
    prob  : Event Ω → R
    cprob : Event Ω → Event Ω → R

    prob-ext :
      {A B : Event Ω} →
      ((ω : Ω) → A ω ↔ B ω) →
      prob A ≡ prob B

    prob-false : prob ev-false ≡ zero
    prob-true  : prob ev-true ≡ one

    prob-union :
      (A B : Event Ω) →
      prob (ev-union A B) ≡
      add (prob A)
          (add (prob B) (opp (prob (ev-inter A B))))

    prob-compl :
      (A : Event Ω) →
      prob (ev-compl A) ≡ add one (opp (prob A))

    excluded-middle : (P : Set) → P ∨ ¬ P

    cprob-mul :
      (A B : Event Ω) →
      prob (ev-inter A B) ≡ mul (cprob A B) (prob B)

    opp-zero      : opp zero ≡ zero
    opp-opp       : (x : R) → opp (opp x) ≡ x
    opp-mul-right : (x y : R) →
                    mul x (opp y) ≡ opp (mul x y)
    opp-mul-left  : (x y : R) →
                    mul (opp x) y ≡ opp (mul x y)

    prob-union-disjoint :
      (A B : Event Ω) →
      Disjoint A B →
      prob (ev-union A B) ≡ add (prob A) (prob B)

    disjoint-head-tail :
      (A : Event Ω) (xs : MyList (Event Ω)) →
      PairwiseDisjoint (A ∷L xs) →
      Disjoint A (bigUnion xs)

module ProbabilityStatements
  {R Ω : Set}
  (ring : Ring R)
  (context : ProbabilityContext R Ω ring) where

  open Ring ring
  open ProbabilityContext context

  prob-union-comm : Set₁
  prob-union-comm =
    (A B : Event Ω) →
    prob (ev-union A B) ≡ prob (ev-union B A)

  prob-union-idem : Set₁
  prob-union-idem =
    (A : Event Ω) →
    prob (ev-union A A) ≡ prob A

  prob-diff : Set₁
  prob-diff =
    (A B : Event Ω) →
    prob (ev-diff A B) ≡
    add (prob A) (opp (prob (ev-inter A B)))

  bayes-symm : Set₁
  bayes-symm =
    (A B : Event Ω) →
    mul (cprob A B) (prob B) ≡
    mul (cprob B A) (prob A)

  law-total-prob : Set₁
  law-total-prob =
    (A B : Event Ω) →
    prob A ≡
    add (mul (cprob A B) (prob B))
        (mul (cprob A (ev-compl B))
             (prob (ev-compl B)))

  prob-union-indep : Set₁
  prob-union-indep =
    (A B : Event Ω) →
    Indep ring prob A B →
    prob (ev-union A B) ≡
    add (prob A)
      (add (prob B)
        (opp (mul (prob A) (prob B))))

  indep-compl-right : Set₁
  indep-compl-right =
    (A B : Event Ω) →
    Indep ring prob A B →
    Indep ring prob A (ev-compl B)

  indep-symm : Set₁
  indep-symm =
    (A B : Event Ω) →
    Indep ring prob A B →
    Indep ring prob B A

  indep-compl-left : Set₁
  indep-compl-left =
    (A B : Event Ω) →
    Indep ring prob A B →
    Indep ring prob (ev-compl A) B

  indep-compl-both : Set₁
  indep-compl-both =
    (A B : Event Ω) →
    Indep ring prob A B →
    Indep ring prob (ev-compl A) (ev-compl B)

  prob-bigUnion-disjoint : Set₁
  prob-bigUnion-disjoint =
    (xs : MyList (Event Ω)) →
    PairwiseDisjoint xs →
    prob (bigUnion xs) ≡
    fold-add add zero (mapL prob xs)

  prob-bigUnion-disjoint-zero : Set₁
  prob-bigUnion-disjoint-zero =
    (xs : MyList (Event Ω)) →
    PairwiseDisjoint xs →
    ((A : Event Ω) → A ∈L xs → prob A ≡ zero) →
    prob (bigUnion xs) ≡ zero

  inclusion-exclusion-three : Set₁
  inclusion-exclusion-three =
    (A B C : Event Ω) →
    prob (ev-union (ev-union A B) C) ≡
    add (prob A)
      (add (prob B)
        (add (prob C)
          (opp
            (add (prob (ev-inter A B))
              (add (prob (ev-inter A C))
                (add (prob (ev-inter B C))
                  (opp
                    (prob
                      (ev-inter (ev-inter A B) C)))))))))
