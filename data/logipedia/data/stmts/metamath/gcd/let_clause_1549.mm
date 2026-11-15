$(
  Statement-only formalization of the Logipedia corpus artifact
  gcd.let_clause_1549
  (logipedia__metamath__gcd.let_clause_1549), catalog title
  "gcd.let_clause_1549": for natural numbers m and n, positivity of n and
  m being zero imply that every natural x equals x minus m under truncated
  natural subtraction. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. Native equality and strict order represent the
  source operations. For x and m in NN0,
    if ( m <_ x , x - m , 0 )
  is exactly the source truncated subtraction nat.minus x m. The declaration
  preserves the quantifier order, the otherwise-unused positivity hypothesis
  on n, the hypothesis 0 = m, and the universal conclusion over x. The final
  declaration is the single unproved $a statement encoding; this database
  contains no $p proof declaration.
$)

${
  $d m n x $.

  logipedia-gcd-let-clause-1549 $a |-
    A. m e. NN0 A. n e. NN0
      (
        0 < n
        ->
        (
          0 = m
          ->
          A. x e. NN0
            (
              x
              =
              if (
                m <_ x ,
                ( x - m ) ,
                0
              )
            )
        )
      )
  $.
$}
