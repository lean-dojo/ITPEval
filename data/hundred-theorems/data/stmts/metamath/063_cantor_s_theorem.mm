$(
  Statement-only formalization of "Cantor's Theorem" from Hundred Theorems
  item 063: no set admits a surjection onto its powerset. This file contains
  no proof.
$)

$[ library/set.mm $]

$(
  In SetMM, A e. _V asserts that A is a set, ~P A is its powerset, and
  f : A -onto-> ~P A says that f is a total surjection from A onto that
  powerset. The following declaration is an unproved $a assertion; this
  database contains no $p proof statement.
$)

ht063-cantor $a |- ( A e. _V -> -. E. f f : A -onto-> ~P A ) $.
