$(
  Statement-only formalization of Thousand Theorems corpus artifact Q656645
  (thousand-theorems__metamath__Q656645), "Hilbert's basis theorem": for every
  commutative Noetherian ring R, the univariate polynomial ring R[X] is
  Noetherian. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's Poly1 ` R is the finite-support univariate polynomial ring over R,
  and LNoeR is the class of left-Noetherian rings. For a commutative ring,
  left Noetherianity is exactly the source's Noetherian-ring property.

  The final $a declaration is the single unproved corpus statement. This
  database contains no $p proof statement.
$)

thousand-theorems-q656645-hilbert-basis-theorem $a |-
  A. R e. ( CRing i^i LNoeR )
    ( Poly1 ` R ) e. LNoeR
$.
