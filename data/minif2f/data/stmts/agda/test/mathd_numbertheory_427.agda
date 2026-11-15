-- Statement-only formalization of miniF2F test problem mathd_numbertheory_427. This file
-- contains no proof.

module mathd-numbertheory-427 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; mod-helper)

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc n) = false
natEqual (suc m) zero = false
natEqual (suc m) (suc n) = natEqual m n

booleanNot : Bool → Bool
booleanNot false = true
booleanNot true = false

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

hasDivisorFrom : Nat → Nat → Nat → Bool
hasDivisorFrom number candidate zero = false
hasDivisorFrom number candidate (suc count)
  with natEqual (naturalMod number candidate) zero
... | true = true
... | false =
  hasDivisorFrom number (suc candidate) count

isPrime : Nat → Bool
isPrime zero = false
isPrime (suc zero) = false
isPrime (suc (suc n)) =
  booleanNot (hasDivisorFrom (suc (suc n)) 2 n)

sumDivisorsUpTo : Nat → Nat → Nat
sumDivisorsUpTo number zero = zero
sumDivisorsUpTo number (suc bound)
  with natEqual (naturalMod number (suc bound)) zero
... | true =
  suc bound + sumDivisorsUpTo number bound
... | false =
  sumDivisorsUpTo number bound

sumDivisors : Nat → Nat
sumDivisors number = sumDivisorsUpTo number number

sumPrimeDivisorsUpTo : Nat → Nat → Nat
sumPrimeDivisorsUpTo number zero = zero
sumPrimeDivisorsUpTo number (suc bound)
  with natEqual (naturalMod number (suc bound)) zero
     | isPrime (suc bound)
... | true | true =
  suc bound + sumPrimeDivisorsUpTo number bound
... | true | false =
  sumPrimeDivisorsUpTo number bound
... | false | true =
  sumPrimeDivisorsUpTo number bound
... | false | false =
  sumPrimeDivisorsUpTo number bound

sumPrimeDivisors : Nat → Nat
sumPrimeDivisors number =
  sumPrimeDivisorsUpTo number number

mathd-numbertheory-427 : Set
mathd-numbertheory-427 =
  (a : Nat) →
  a ≡ sumDivisors 500 →
  sumPrimeDivisors a ≡ 25
