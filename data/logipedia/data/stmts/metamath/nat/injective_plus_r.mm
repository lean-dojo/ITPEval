$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.injective_plus_r (logipedia__metamath__nat.injective_plus_r), catalog
  title "nat.injective_plus_r": for every natural number n, the function
  sending m to n + m is injective. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM's total addition and native equality represent
  the source plus operation and natural-number equality. Expanding
  relations.injective gives the restricted universal quantifiers over m and k
  and the implication from equality of their images under addition by n to
  equality of m and k. The final declaration is Metamath's native unproved $a
  statement encoding; this artifact adds no $p proof declaration.
$)

${
  $d n m k $.

  logipedia-nat-injective-plus-r $a |-
    A. n e. NN0
      A. m e. NN0
        A. k e. NN0
          (
            ( n + m ) = ( n + k )
            ->
            m = k
          )
  $.
$}
