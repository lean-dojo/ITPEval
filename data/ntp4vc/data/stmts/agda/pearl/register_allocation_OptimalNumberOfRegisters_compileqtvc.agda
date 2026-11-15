-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/register_allocation_OptimalNumberOfRegisters_compileqtvc: the
-- verification condition for compiling expression trees using the
-- recursively computed minimal register requirement to choose evaluation
-- order, with stack spilling when the register supply is exhausted.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module register_allocation_OptimalNumberOfRegisters_compileqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_
infixr 3 _∧_
infixr 2 _∨_

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record Exists (A : Set) (P : A → Set) : Set where
  constructor exists
  field
    witness  : A
    property : P witness

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

intEqual : Int → Int → Bool
intEqual (pos m) (pos n) = natEqual m n
intEqual (pos _) (negsuc _) = false
intEqual (negsuc _) (pos _) = false
intEqual (negsuc m) (negsuc n) = natEqual m n

intLessOrEqual : Int → Int → Bool
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos _) (negsuc _) = false
intLessOrEqual (negsuc _) (pos _) = true
intLessOrEqual (negsuc m) (negsuc n) = natLessOrEqual n m

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos _) (negsuc _) = false
intLess (negsuc _) (pos _) = true
intLess (negsuc m) (negsuc n) = natLess n m

_≤Z_ : Int → Int → Set
x ≤Z y = intLessOrEqual x y ≡ true

_<Z_ : Int → Int → Set
x <Z y = intLess x y ≡ true

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

negateInt : Int → Int
negateInt (pos n) = negative n
negateInt (negsuc n) = pos (suc n)

differenceNat : Nat → Nat → Int
differenceNat zero zero = pos zero
differenceNat (suc m) zero = pos (suc m)
differenceNat zero (suc n) = negsuc n
differenceNat (suc m) (suc n) = differenceNat m n

addInt : Int → Int → Int
addInt (pos m) (pos n) = pos (m + n)
addInt (pos m) (negsuc n) = differenceNat m (suc n)
addInt (negsuc m) (pos n) = differenceNat n (suc m)
addInt (negsuc m) (negsuc n) = negsuc (suc (m + n))

subtractInt : Int → Int → Int
subtractInt x y = addInt x (negateInt y)

zeroZ oneZ twoZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos (suc (suc zero))

ExcludedMiddle : Set₁
ExcludedMiddle = (P : Set) → P ∨ Not P

truthValue : ExcludedMiddle → Set → Bool
truthValue excludedMiddle P with excludedMiddle P
... | left _ = true
... | right _ = false

FunctionEqual :
  {A B : Set} →
  (A → B) →
  (A → B) →
  Set
FunctionEqual f g = (x : _) → f x ≡ g x

data Expr (Addr : Set) : Set where
  Evar : Addr → Expr Addr
  Eneg : Expr Addr → Expr Addr
  Eadd : Expr Addr → Expr Addr → Expr Addr

maxInt : Int → Int → Int
maxInt x y with intLessOrEqual x y
... | true = y
... | false = x

nRegisters : {Addr : Set} → Expr Addr → Int
nRegisters (Evar _) = oneZ
nRegisters (Eneg expression) = nRegisters expression
nRegisters (Eadd leftExpression rightExpression) with
  intEqual (nRegisters leftExpression) (nRegisters rightExpression)
... | true = addInt oneZ (nRegisters leftExpression)
... | false =
  maxInt (nRegisters leftExpression) (nRegisters rightExpression)

measure : {Addr : Set} → Expr Addr → Int
measure (Evar _) = zeroZ
measure (Eneg expression) = addInt oneZ (measure expression)
measure (Eadd leftExpression rightExpression) with
  intLessOrEqual (nRegisters rightExpression) (nRegisters leftExpression)
... | true =
  addInt oneZ (addInt (measure leftExpression) (measure rightExpression))
... | false =
  addInt
    oneZ
    (addInt
      oneZ
      (addInt (measure leftExpression) (measure rightExpression)))

eval :
  {Addr : Set} →
  (Addr → Int) →
  Expr Addr →
  Int
eval memory (Evar address) = memory address
eval memory (Eneg expression) = negateInt (eval memory expression)
eval memory (Eadd leftExpression rightExpression) =
  addInt (eval memory leftExpression) (eval memory rightExpression)

data Instr (Addr : Set) : Set where
  Iload : Addr → Int → Instr Addr
  Ineg  : Int → Instr Addr
  Iadd  : Int → Int → Instr Addr
  Ipush : Int → Instr Addr
  Ipop  : Int → Instr Addr

record State (Addr : Set) : Set where
  constructor state
  field
    mem : Addr → Int
    reg : Int → Int
    st  : List Int

open State public

updateRegisters : (Int → Int) → Int → Int → Int → Int
updateRegisters old key value query with intEqual query key
... | true = value
... | false = old query

exec : {Addr : Set} → Instr Addr → State Addr → State Addr
exec (Iload address register) s =
  state
    (mem s)
    (updateRegisters (reg s) register (mem s address))
    (st s)
exec (Ineg register) s =
  state
    (mem s)
    (updateRegisters (reg s) register (negateInt (reg s register)))
    (st s)
exec (Iadd source target) s =
  state
    (mem s)
    (updateRegisters
      (reg s)
      target
      (addInt (reg s source) (reg s target)))
    (st s)
exec (Ipush register) s =
  state (mem s) (reg s) (reg s register ∷ st s)
exec (Ipop register) s with st s
... | [] = s
... | value ∷ rest =
  state
    (mem s)
    (updateRegisters (reg s) register value)
    rest

execList :
  {Addr : Set} →
  List (Instr Addr) →
  State Addr →
  State Addr
execList [] s = s
execList (instruction ∷ program) s =
  execList program (exec instruction s)

Post : Set → Set
Post Addr = State Addr → State Addr → Bool

ExprPostProperty :
  {Addr : Set} →
  Expr Addr →
  Int →
  State Addr →
  State Addr →
  Set
ExprPostProperty expression register initial final =
  FunctionEqual (mem final) (mem initial)
  ∧
  (reg final register ≡ eval (mem initial) expression)
  ∧
  (st final ≡ st initial)
  ∧
  ((lower : Int) →
   lower <Z register →
   reg final lower ≡ reg initial lower)

exprPost :
  {Addr : Set} →
  ExcludedMiddle →
  Expr Addr →
  Int →
  Post Addr
exprPost excludedMiddle expression register initial final =
  truthValue excludedMiddle
    (ExprPostProperty expression register initial final)

record HCode (Addr : Set) : Set where
  constructor hcode
  field
    hcode1 : List (Instr Addr)
    post1  : Post Addr

open HCode public

HCodeOK : {Addr : Set} → HCode Addr → Set
HCodeOK hc =
  (s : State _) →
  post1 hc s (execList (hcode1 hc) s) ≡ true

Trans : Set → Set
Trans Addr = (State Addr → Bool) → State Addr → Bool

record WCode (Addr : Set) : Set where
  constructor wcode
  field
    trans1 : Trans Addr
    wcode1 : List (Instr Addr)

open WCode public

WCodeOK : {Addr : Set} → WCode Addr → Set
WCodeOK wc =
  (q : State _ → Bool) →
  (s : State _) →
  trans1 wc q s ≡ true →
  q (execList (wcode1 wc) s) ≡ true

identity : {Addr : Set} → Trans Addr
identity q = q

execClosure :
  {Addr : Set} →
  Instr Addr →
  State Addr →
  State Addr
execClosure = exec

rcompose :
  {A B C : Set} →
  (A → B) →
  (B → C) →
  A →
  C
rcompose f g x = g (f x)

toWP :
  {Addr : Set} →
  ExcludedMiddle →
  Post Addr →
  Trans Addr
toWP excludedMiddle pst q initial =
  truthValue excludedMiddle
    ((final : State _) →
     pst initial final ≡ true →
     q final ≡ true)

PostEqual :
  {Addr : Set} →
  Post Addr →
  Post Addr →
  Set
PostEqual leftPost rightPost =
  (initial final : State _) →
  leftPost initial final ≡ rightPost initial final

TransEqual :
  {Addr : Set} →
  Trans Addr →
  Trans Addr →
  Set
TransEqual leftTrans rightTrans =
  (q : State _ → Bool) →
  (s : State _) →
  leftTrans q s ≡ rightTrans q s

MeasureDecrease :
  {Addr : Set} →
  Expr Addr →
  Expr Addr →
  Set
MeasureDecrease whole recursiveArgument =
  zeroZ ≤Z measure whole
  ∧ measure recursiveArgument <Z measure whole

InitialWCode :
  {Addr : Set} →
  WCode Addr →
  Set
InitialWCode wc =
  WCodeOK wc ∧ TransEqual (trans1 wc) identity

OrderedRecursiveObligations :
  {Addr : Set} →
  ExcludedMiddle →
  Int →
  Int →
  Expr Addr →
  Expr Addr →
  Expr Addr →
  Set
OrderedRecursiveObligations
  {Addr} excludedMiddle k r expression e1 e2 =
  IfSet
    (intLess r (subtractInt k oneZ))
    ((o2 : WCode Addr) →
     InitialWCode o2 →
     WCodeOK o2
     ∧
     ((o3 : WCode _) →
      (WCodeOK o3
       ∧
       TransEqual
         (trans1 o3)
         (rcompose
           (trans1 o2)
           (rcompose
             (execClosure (Iadd (addInt r oneZ) r))))) →
      let o4 = addInt r oneZ
      in
      (MeasureDecrease expression e2
       ∧
       (zeroZ ≤Z o4 ∧ o4 <Z k))
      ∧
      ((o5 : HCode _) →
       (HCodeOK o5
        ∧
        PostEqual
          (post1 o5)
          (exprPost excludedMiddle e2 o4)) →
       HCodeOK o5
       ∧
       ((o6 : WCode _) →
        (WCodeOK o6
         ∧
         TransEqual
           (trans1 o6)
           (toWP excludedMiddle (post1 o5))) →
        (MeasureDecrease expression e1
         ∧
         (zeroZ ≤Z r ∧ r <Z k))
        ∧
        ((o7 : HCode _) →
         (HCodeOK o7
          ∧
          PostEqual
            (post1 o7)
            (exprPost excludedMiddle e1 r)) →
         HCodeOK o7
         ∧
         ((o8 : WCode _) →
          (WCodeOK o8
           ∧
           TransEqual
             (trans1 o8)
             (toWP excludedMiddle (post1 o7))) →
          (WCodeOK o8 ∧ WCodeOK o6)
          ∧
          ((o9 : WCode _) →
           (WCodeOK o9
            ∧
            TransEqual
              (trans1 o9)
              (rcompose (trans1 o6) (trans1 o8))) →
           WCodeOK o9 ∧ WCodeOK o3)))))))
    ((o2 : WCode _) →
     InitialWCode o2 →
     WCodeOK o2
     ∧
     ((o3 : WCode _) →
      (WCodeOK o3
       ∧
       TransEqual
         (trans1 o3)
         (rcompose
           (trans1 o2)
           (rcompose
             (execClosure (Ipop (subtractInt k twoZ)))))) →
      WCodeOK o3
      ∧
      ((o4 : WCode _) →
       (WCodeOK o4
        ∧
        TransEqual
          (trans1 o4)
          (rcompose
            (trans1 o3)
            (rcompose
              (execClosure
                (Iadd
                  (subtractInt k twoZ)
                  (subtractInt k oneZ)))))) →
       let o5 = subtractInt k oneZ
       in
       (MeasureDecrease expression e2
        ∧
        (zeroZ ≤Z o5 ∧ o5 <Z k))
       ∧
       ((o6 : HCode _) →
        (HCodeOK o6
         ∧
         PostEqual
           (post1 o6)
           (exprPost excludedMiddle e2 o5)) →
        HCodeOK o6
        ∧
        ((o7 : WCode _) →
         (WCodeOK o7
          ∧
          TransEqual
            (trans1 o7)
            (toWP excludedMiddle (post1 o6))) →
         let o8 = subtractInt k twoZ
         in
         (MeasureDecrease expression e1
          ∧
          (zeroZ ≤Z o8 ∧ o8 <Z k))
         ∧
         ((o9 : HCode _) →
          (HCodeOK o9
           ∧
           PostEqual
             (post1 o9)
             (exprPost excludedMiddle e1 o8)) →
          HCodeOK o9
          ∧
          ((o10 : WCode _) →
           (WCodeOK o10
            ∧
            TransEqual
              (trans1 o10)
              (toWP excludedMiddle (post1 o9))) →
           (WCodeOK o10 ∧ WCodeOK o7)
           ∧
           ((o11 : WCode _) →
            (WCodeOK o11
             ∧
             TransEqual
               (trans1 o11)
               (rcompose (trans1 o7) (trans1 o10))) →
            (WCodeOK o11 ∧ WCodeOK o4)
            ∧
            ((o12 : WCode _) →
             (WCodeOK o12
              ∧
              TransEqual
                (trans1 o12)
                (rcompose (trans1 o4) (trans1 o11))) →
             WCodeOK o12)))))))))

SwappedRecursiveObligations :
  {Addr : Set} →
  ExcludedMiddle →
  Int →
  Int →
  Expr Addr →
  Expr Addr →
  Expr Addr →
  Set
SwappedRecursiveObligations
  {Addr} excludedMiddle k r expression e1 e2 =
  (MeasureDecrease expression (Eadd e2 e1)
   ∧
   (zeroZ ≤Z r ∧ r <Z k))
  ∧
  ((o3 : HCode Addr) →
   (HCodeOK o3
    ∧
    PostEqual
      (post1 o3)
      (exprPost excludedMiddle (Eadd e2 e1) r)) →
   HCodeOK o3)

RecursiveObligations :
  {Addr : Set} →
  ExcludedMiddle →
  Int →
  Int →
  Expr Addr →
  Set
RecursiveObligations {Addr} excludedMiddle k r (Evar address) =
  (o2 : WCode Addr) →
  InitialWCode o2 →
  WCodeOK o2
RecursiveObligations {Addr} excludedMiddle k r expression@(Eneg e1) =
  (o2 : WCode Addr) →
  InitialWCode o2 →
  WCodeOK o2
  ∧
  ((o3 : WCode _) →
   (WCodeOK o3
    ∧
    TransEqual
      (trans1 o3)
      (rcompose
        (trans1 o2)
        (rcompose (execClosure (Ineg r))))) →
   ((MeasureDecrease expression e1
     ∧
     (zeroZ ≤Z r ∧ r <Z k))
    ∧
    ((o4 : HCode _) →
     (HCodeOK o4
      ∧
      PostEqual (post1 o4) (exprPost excludedMiddle e1 r)) →
     HCodeOK o4
     ∧
     ((o5 : WCode _) →
      (WCodeOK o5
       ∧
       TransEqual
         (trans1 o5)
         (toWP excludedMiddle (post1 o4))) →
      WCodeOK o5 ∧ WCodeOK o3))))
RecursiveObligations {Addr} excludedMiddle k r expression@(Eadd e1 e2) =
  IfSet
    (intLessOrEqual (nRegisters e2) (nRegisters e1))
    (OrderedRecursiveObligations
      excludedMiddle k r expression e1 e2)
    (SwappedRecursiveObligations
      excludedMiddle k r expression e1 e2)

ConstructionPremise :
  {Addr : Set} →
  ExcludedMiddle →
  Int →
  Int →
  Expr Addr →
  WCode Addr →
  Set
ConstructionPremise {Addr} excludedMiddle k r (Evar address) o2 =
  Exists (WCode Addr)
    (λ o3 →
      InitialWCode o3
      ∧
      (WCodeOK o2
       ∧
       TransEqual
         (trans1 o2)
         (rcompose
           (trans1 o3)
           (rcompose (execClosure (Iload address r))))))
ConstructionPremise {Addr} excludedMiddle k r (Eneg e1) o2 =
  Exists (WCode Addr)
    (λ o3 →
      InitialWCode o3
      ∧
      Exists (WCode _)
        (λ o4 →
          (WCodeOK o4
           ∧
           TransEqual
             (trans1 o4)
             (rcompose
               (trans1 o3)
               (rcompose (execClosure (Ineg r)))))
          ∧
          Exists (HCode _)
            (λ o5 →
              (HCodeOK o5
               ∧
               PostEqual
                 (post1 o5)
                 (exprPost excludedMiddle e1 r))
              ∧
              Exists (WCode _)
                (λ o6 →
                  (WCodeOK o6
                   ∧
                   TransEqual
                     (trans1 o6)
                     (toWP excludedMiddle (post1 o5)))
                  ∧
                  (WCodeOK o2
                   ∧
                   TransEqual
                     (trans1 o2)
                     (rcompose (trans1 o4) (trans1 o6)))))))
ConstructionPremise {Addr} excludedMiddle k r (Eadd e1 e2) o2 =
  IfSet
    (intLessOrEqual (nRegisters e2) (nRegisters e1))
    (IfSet
      (intLess r (subtractInt k oneZ))
      (Exists (WCode Addr)
      (λ o3 →
        InitialWCode o3
        ∧
        Exists (WCode _)
          (λ o4 →
            (WCodeOK o4
             ∧
             TransEqual
               (trans1 o4)
               (rcompose
                 (trans1 o3)
                 (rcompose
                   (execClosure (Iadd (addInt r oneZ) r)))))
            ∧
            Exists (HCode _)
              (λ o5 →
                (HCodeOK o5
                 ∧
                 PostEqual
                   (post1 o5)
                   (exprPost excludedMiddle e2 (addInt r oneZ)))
                ∧
                Exists (WCode _)
                  (λ o6 →
                    (WCodeOK o6
                     ∧
                     TransEqual
                       (trans1 o6)
                       (toWP excludedMiddle (post1 o5)))
                    ∧
                    Exists (HCode _)
                      (λ o7 →
                        (HCodeOK o7
                         ∧
                         PostEqual
                           (post1 o7)
                           (exprPost excludedMiddle e1 r))
                        ∧
                        Exists (WCode _)
                          (λ o8 →
                            (WCodeOK o8
                             ∧
                             TransEqual
                               (trans1 o8)
                               (toWP excludedMiddle (post1 o7)))
                            ∧
                            Exists (WCode _)
                              (λ o9 →
                                (WCodeOK o9
                                 ∧
                                 TransEqual
                                   (trans1 o9)
                                   (rcompose
                                     (trans1 o6)
                                     (trans1 o8)))
                                ∧
                                (WCodeOK o2
                                 ∧
                                 TransEqual
                                   (trans1 o2)
                                   (rcompose
                                     (trans1 o4)
                                     (trans1 o9)))))))))))
      (Exists (WCode Addr)
      (λ o3 →
        InitialWCode o3
        ∧
        Exists (WCode _)
          (λ o4 →
            (WCodeOK o4
             ∧
             TransEqual
               (trans1 o4)
               (rcompose
                 (trans1 o3)
                 (rcompose
                   (execClosure (Ipop (subtractInt k twoZ))))))
            ∧
            Exists (WCode _)
              (λ o5 →
                (WCodeOK o5
                 ∧
                 TransEqual
                   (trans1 o5)
                   (rcompose
                     (trans1 o4)
                     (rcompose
                       (execClosure
                         (Iadd
                           (subtractInt k twoZ)
                           (subtractInt k oneZ))))))
                ∧
                Exists (HCode _)
                  (λ o6 →
                    (HCodeOK o6
                     ∧
                     PostEqual
                       (post1 o6)
                       (exprPost
                         excludedMiddle
                         e2
                         (subtractInt k oneZ)))
                    ∧
                    Exists (WCode _)
                      (λ o7 →
                        (WCodeOK o7
                         ∧
                         TransEqual
                           (trans1 o7)
                           (toWP excludedMiddle (post1 o6)))
                        ∧
                        Exists (HCode _)
                          (λ o8 →
                            (HCodeOK o8
                             ∧
                             PostEqual
                               (post1 o8)
                               (exprPost
                                 excludedMiddle
                                 e1
                                 (subtractInt k twoZ)))
                            ∧
                            Exists (WCode _)
                              (λ o9 →
                                (WCodeOK o9
                                 ∧
                                 TransEqual
                                   (trans1 o9)
                                   (toWP excludedMiddle (post1 o8)))
                                ∧
                                Exists (WCode _)
                                  (λ o10 →
                                    (WCodeOK o10
                                     ∧
                                     TransEqual
                                       (trans1 o10)
                                       (rcompose
                                         (trans1 o7)
                                         (trans1 o9)))
                                    ∧
                                    Exists (WCode _)
                                      (λ o11 →
                                        (WCodeOK o11
                                         ∧
                                         TransEqual
                                           (trans1 o11)
                                           (rcompose
                                             (trans1 o5)
                                             (trans1 o10)))
                                        ∧
                                        (WCodeOK o2
                                         ∧
                                         TransEqual
                                           (trans1 o2)
                                           (rcompose
                                             (trans1 o11)
                                             (rcompose
                                               (execClosure
                                                 (Ipush
                                                   (subtractInt
                                                     k
                                                     twoZ)))))))))))))))))
    (Exists (HCode Addr)
      (λ o3 →
        (HCodeOK o3
         ∧
         PostEqual
           (post1 o3)
           (exprPost excludedMiddle (Eadd e2 e1) r))
        ∧
        (WCodeOK o2
         ∧
         TransEqual
           (trans1 o2)
           (toWP excludedMiddle (post1 o3)))))

ConstructionConclusion :
  {Addr : Set} →
  ExcludedMiddle →
  Int →
  Expr Addr →
  WCode Addr →
  Set
ConstructionConclusion {Addr} excludedMiddle r expression o2 =
  (WCodeOK o2
   ∧
   ((x : State Addr) →
    trans1 o2 (exprPost excludedMiddle expression r x) x ≡ true))
  ∧
  ((result : HCode Addr) →
   (HCodeOK result
    ∧
    PostEqual
      (post1 result)
      (exprPost excludedMiddle expression r)) →
   HCodeOK result
   ∧
   PostEqual
     (post1 result)
     (exprPost excludedMiddle expression r))

CompileVC :
  {Addr : Set} →
  ExcludedMiddle →
  Int →
  Int →
  Expr Addr →
  Set
CompileVC {Addr} excludedMiddle k r expression =
  RecursiveObligations excludedMiddle k r expression
  ∧
  ((o2 : WCode Addr) →
   ConstructionPremise excludedMiddle k r expression o2 →
   ConstructionConclusion excludedMiddle r expression o2)

compile'vc : Set₁
compile'vc =
  (Addr : Set) →
  (addrWitness : Addr) →
  (excludedMiddle : ExcludedMiddle) →
  (k : Int) →
  twoZ ≤Z k →
  (r : Int) →
  (expression : Expr Addr) →
  zeroZ ≤Z r →
  r <Z k →
  CompileVC excludedMiddle k r expression
