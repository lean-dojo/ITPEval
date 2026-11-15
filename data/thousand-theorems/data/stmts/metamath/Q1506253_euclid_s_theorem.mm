$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1506253
  (thousand-theorems__metamath__Q1506253), "Euclid's theorem": for every
  natural number n, there exists a prime number p with n less than or equal
  to p. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers, faithfully representing
  Lean's natural-number domain. Prime is the class of natural prime numbers,
  and <_ is non-strict arithmetic order. Thus the bounded quantifiers and
  conclusion directly encode the source statement
  (n : Nat) -> exists p, n <= p and Nat.Prime p.

  The final declaration is the single unproved $a corpus statement; this
  candidate root file contains no $p statement.
$)

thousand-theorems-q1506253-euclid-s-theorem $a
  |- A. n e. NN0 E. p e. Prime n <_ p
$.
