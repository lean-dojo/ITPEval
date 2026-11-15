$(
  Statement-only formalization of Thousand Theorems corpus artifact Q943246
  (thousand-theorems__metamath__Q943246), "Wedderburn's little theorem":
  every division ring with finite carrier is a field. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  In SetMM, DivRing is the class of division-ring structures, Base gives the
  carrier of a structure, Fin is the class of finite sets, and Field is the
  intersection of DivRing with the class of commutative rings. Thus the
  conclusion says that multiplication in the same finite division-ring
  structure is commutative.

  The declaration below is the single unproved $a corpus statement. This
  database contains no $p proof statement.
$)

${
  thousand-theorems-q943246-wedderburn-s-little-theorem $a |-
    A. D e. DivRing
      ( ( Base ` D ) e. Fin -> D e. Field )
  $.
$}
