$(
  Statement-only formalization of Thousand Theorems corpus artifact Q474881
  (thousand-theorems__metamath__Q474881), "Cantor's theorem": no arbitrary set
  admits a surjection onto its powerset. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  In SetMM, A e. _V asserts that A is a set, ~P A is its powerset, and
  f : A -onto-> ~P A says that f is a total surjection from A onto that
  powerset. Negating the existence of such an f is equivalent to the Lean
  statement that every function from an arbitrary type to its set of subsets
  is not surjective. The declaration below is the single unproved corpus $a
  statement; this database contains no $p proof statement.
$)

thousand-theorems-q474881-cantor $a |-
  ( A e. _V -> -. E. f f : A -onto-> ~P A )
$.
