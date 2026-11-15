$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1988_b2: a real inequality implication involving two quadratic
  expressions in nonnegative y and arbitrary real x. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  The Rocq source defines the solution proposition as True, and the Lean and
  Isabelle sources annotate the same intended solution. Therefore their
  biconditional with the universal implication is logically equivalent to
  asserting the universal implication directly below.

  SetMM's RR is the class of real numbers. Both variables remain universally
  quantified over RR, and the nonnegativity and quadratic comparison are the
  antecedent of the implication. The final declaration is the single unproved
  $a corpus statement; this database contains no $p proof statement.
$)

${
  $d x y $.

  putnambench-putnam-1988-b2 $a |-
    A. x e. RR A. y e. RR
      (
        (
          0 <_ y
          /\
          ( y x. ( y + 1 ) ) <_ ( ( x + 1 ) ^ 2 )
        )
        ->
        ( y x. ( y - 1 ) ) <_ ( x ^ 2 )
      )
  $.
$}
