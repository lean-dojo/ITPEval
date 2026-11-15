-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/register_allocation_InfinityOfRegisters_compileqtvc: the verification
-- condition for compiling expression trees with an unbounded supply of
-- integer-indexed registers while preserving memory, stack, and lower registers.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module register_allocation_InfinityOfRegisters_compileqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _<Z_
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

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

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

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos _) (negsuc _) = false
intLess (negsuc _) (pos _) = true
intLess (negsuc m) (negsuc n) = natLess n m

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

oneZ : Int
oneZ = pos (suc zero)

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

ImmediateSubexpression :
  {Addr : Set} →
  Expr Addr →
  Expr Addr →
  Set
ImmediateSubexpression (Evar _) candidate = ⊥
ImmediateSubexpression (Eneg expression) candidate =
  expression ≡ candidate
ImmediateSubexpression (Eadd leftExpression rightExpression) candidate =
  (leftExpression ≡ candidate) ∨ (rightExpression ≡ candidate)

InitialWCode :
  {Addr : Set} →
  WCode Addr →
  Set
InitialWCode wc =
  WCodeOK wc ∧ TransEqual (trans1 wc) identity

RecursiveObligations :
  {Addr : Set} →
  ExcludedMiddle →
  Int →
  Expr Addr →
  Set
RecursiveObligations {Addr} excludedMiddle r (Evar address) =
  (o2 : WCode Addr) →
  InitialWCode o2 →
  WCodeOK o2
RecursiveObligations {Addr} excludedMiddle r expression@(Eneg e1) =
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
   ImmediateSubexpression expression e1
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
     WCodeOK o5 ∧ WCodeOK o3)))
RecursiveObligations {Addr} excludedMiddle r expression@(Eadd e1 e2) =
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
        (rcompose
          (execClosure (Iadd (addInt r oneZ) r))))) →
   ImmediateSubexpression expression e2
   ∧
   ((o4 : HCode _) →
    (HCodeOK o4
     ∧
     PostEqual
       (post1 o4)
       (exprPost excludedMiddle e2 (addInt r oneZ))) →
    HCodeOK o4
    ∧
    ((o5 : WCode _) →
     (WCodeOK o5
      ∧
      TransEqual
        (trans1 o5)
        (toWP excludedMiddle (post1 o4))) →
     ImmediateSubexpression expression e1
     ∧
     ((o6 : HCode _) →
      (HCodeOK o6
       ∧
       PostEqual
         (post1 o6)
         (exprPost excludedMiddle e1 r)) →
      HCodeOK o6
      ∧
      ((o7 : WCode _) →
       (WCodeOK o7
        ∧
        TransEqual
          (trans1 o7)
          (toWP excludedMiddle (post1 o6))) →
       (WCodeOK o7 ∧ WCodeOK o5)
       ∧
       ((o8 : WCode _) →
        (WCodeOK o8
         ∧
         TransEqual
           (trans1 o8)
           (rcompose (trans1 o5) (trans1 o7))) →
        WCodeOK o8 ∧ WCodeOK o3))))))

ConstructionPremise :
  {Addr : Set} →
  ExcludedMiddle →
  Int →
  Expr Addr →
  WCode Addr →
  Set
ConstructionPremise {Addr} excludedMiddle r (Evar address) o2 =
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
ConstructionPremise {Addr} excludedMiddle r (Eneg e1) o2 =
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
ConstructionPremise {Addr} excludedMiddle r (Eadd e1 e2) o2 =
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
                                   (trans1 o9))))))))))

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
  Expr Addr →
  Set
CompileVC {Addr} excludedMiddle r expression =
  RecursiveObligations excludedMiddle r expression
  ∧
  ((o2 : WCode Addr) →
   ConstructionPremise excludedMiddle r expression o2 →
   ConstructionConclusion excludedMiddle r expression o2)

compile'vc : Set₁
compile'vc =
  (Addr : Set) →
  (addrWitness : Addr) →
  (excludedMiddle : ExcludedMiddle) →
  (expression : Expr Addr) →
  (r : Int) →
  CompileVC excludedMiddle r expression
