$(
  Statement-only formalization of Hundred Theorems item 025,
  "Schroeder-Bernstein Theorem": for arbitrary sets, injections in both
  directions imply a bijection. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  In SetMM, A ~<_ B means that there exists a one-to-one function from A to
  B, while A ~~ B means that A and B are equipollent, equivalently that a
  bijection exists between them.

  ht025-schroeder-bernstein is an unproved $a assertion. This file contains
  no $p proof statement.
$)

ht025-schroeder-bernstein $a |- (
  ( A ~<_ B /\ B ~<_ A )
  ->
  A ~~ B
) $.
