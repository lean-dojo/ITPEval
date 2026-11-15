$(
  Statement-only formalization of the Logipedia corpus artifact
  gcd.let_clause_15491 (logipedia__metamath__gcd.let_clause_15491), catalog
  title "gcd.let_clause_15491": for natural numbers m and n, if n is zero,
  then every natural number is unchanged by truncated subtraction of n. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. Native equality represents logic.eq. For x and n in
  NN0,
    if ( n <_ x , x - n , 0 )
  is exactly the source truncated subtraction nat.minus x n. The declaration
  preserves the unused outer parameter m, the quantifier order, the hypothesis
  0 = n, and the universal conclusion over x. The final declaration is the
  artifact's single unproved $a statement encoding; this artifact adds no $p
  proof declaration.
$)

${
  $d m n x $.

  logipedia-gcd-let-clause-15491 $a |-
    A. m e. NN0 A. n e. NN0
      (
        0 = n
        ->
        A. x e. NN0
          (
            x
            =
            if (
              n <_ x ,
              ( x - n ) ,
              0
            )
          )
      )
  $.
$}
