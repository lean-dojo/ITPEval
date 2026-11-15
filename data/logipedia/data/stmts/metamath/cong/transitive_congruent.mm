$(
  Statement-only formalization of the Logipedia corpus artifact
  cong.transitive_congruent, catalog title "cong.transitive_congruent":
  equality under the source's total natural remainder operation is transitive
  for every natural modulus. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is the source natural-number domain. The source remainder div_mod.mod
  u p equals u when p = 0 and the ordinary natural remainder ( u mod p )
  when p is positive. Thus if ( p = 0 , u , ( u mod p ) ) is its exact
  total SetMM encoding. Expanding congruent as equality of these remainders
  and relations.transitive gives the three universally quantified natural
  numbers and two nested implications below, with no positivity assumption
  on p. The declaration is an unproved $a statement encoding; this database
  contains no $p proof declaration.
$)

${
  $d p x y z $.

  logipedia-cong-transitive-congruent $a |-
    A. p e. NN0 A. x e. NN0 A. y e. NN0 A. z e. NN0
      (
        if ( p = 0 , x , ( x mod p ) )
          = if ( p = 0 , y , ( y mod p ) )
        ->
        (
          if ( p = 0 , y , ( y mod p ) )
            = if ( p = 0 , z , ( z mod p ) )
          ->
          if ( p = 0 , x , ( x mod p ) )
            = if ( p = 0 , z , ( z mod p ) )
        )
      )
  $.
$}
