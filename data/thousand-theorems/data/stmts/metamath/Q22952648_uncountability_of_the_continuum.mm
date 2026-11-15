$(
  Statement-only formalization of Thousand Theorems corpus artifact Q22952648
  (thousand-theorems__metamath__Q22952648), "Uncountability of the
  continuum": the set of all real numbers is not countable. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  In SetMM, RR is the set of all real numbers and A ~<_ _om means that A
  injects into omega, equivalently that A is at most countable. Its negation
  therefore states exactly that the universal set of real numbers is not
  countable.

  The final declaration is the single unproved $a corpus statement. This file
  adds no $p proof statement.
$)

thousand-theorems-q22952648-uncountability-of-the-continuum $a |-
  -. ( RR ~<_ _om ) $.
