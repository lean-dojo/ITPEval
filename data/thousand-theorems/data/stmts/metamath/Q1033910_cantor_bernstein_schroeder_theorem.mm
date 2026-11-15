$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1033910
  (thousand-theorems__metamath__Q1033910), "Cantor-Bernstein-Schroeder
  theorem": for arbitrary sets, injections in both directions imply a
  bijection. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  In SetMM, A ~<_ B means that there exists a one-to-one function from A to
  B, while A ~~ B means that A and B are equipollent, equivalently that a
  bijection exists between them.

  The final declaration is the single unproved $a corpus statement. This
  file introduces no $p proof statement.
$)

thousand-theorems-q1033910-cantor-bernstein-schroeder $a |- (
  ( A ~<_ B /\ B ~<_ A )
  ->
  A ~~ B
) $.
