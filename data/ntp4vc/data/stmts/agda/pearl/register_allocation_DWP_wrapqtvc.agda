-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/register_allocation_DWP_wrapqtvc: correctness of wrapping a
-- double-weakest-precondition code transformer over a nonempty address domain
-- with a state-indexed postcondition for the register-allocation machine.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module register_allocation_DWP_wrapqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

intEqual : Int → Int → Bool
intEqual (pos m) (pos n) = natEqual m n
intEqual (pos _) (negsuc _) = false
intEqual (negsuc _) (pos _) = false
intEqual (negsuc m) (negsuc n) = natEqual m n

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

wrap'vc : Set₁
wrap'vc =
  (Addr : Set) →
  (addrWitness : Addr) →
  (wc : WCode Addr) →
  (pst : Post Addr) →
  WCodeOK wc →
  ((x : State Addr) → trans1 wc (pst x) x ≡ true) →
  HCodeOK (hcode (wcode1 wc) pst)
