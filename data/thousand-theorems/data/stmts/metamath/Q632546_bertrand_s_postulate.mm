$(
  Statement-only formalization of Thousand Theorems corpus artifact Q632546
  (thousand-theorems__metamath__Q632546), "Bertrand's postulate": for every
  nonzero natural number n, there exists a prime natural number p strictly
  greater than n and at most twice n. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers, faithfully representing the
  source natural-number domain, and Prime is its class of natural prime
  numbers. The antecedent n =/= 0 is exactly the source hypothesis hn0.
  Bounded existential quantification over Prime combines the source witness's
  natural-number type and Nat.Prime condition, while <, <_, and x. are the
  standard arithmetic order and multiplication operations.

  The final declaration is the single unproved $a corpus statement. This root
  file contains no $p proof statement.
$)

thousand-theorems-q632546-bertrand-postulate $a |-
  A. n e. NN0
    (
      n =/= 0
      ->
      E. p e. Prime
        ( n < p /\ p <_ ( 2 x. n ) )
    )
$.
