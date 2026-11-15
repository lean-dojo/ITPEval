$(
  Statement-only formalization of the Logipedia corpus artifact
  permutation.eq_to_bijn (logipedia__metamath__permutation.eq_to_bijn),
  catalog title "permutation.eq_to_bijn": pointwise equality of two
  natural-number endofunctions through a bound preserves bounded
  surjectivity on that initial segment. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 and ( NN0 ^m NN0 ) preserve the source natural-number and total
  endofunction domains. Each occurrence of the source predicate bijn is
  unfolded: every m at most n has a preimage p at most n. Native SetMM
  equality bidirectionally represents the source equality predicate on
  natural numbers. The nested implications preserve the source assumptions
  and conclusion. The final declaration is Metamath's native unproved $a
  statement encoding; this artifact adds no $p proof declaration.
$)

${
  $d f g i m n p $.

  logipedia-permutation-eq-to-bijn $a |-
    A. f e. ( NN0 ^m NN0 )
      A. g e. ( NN0 ^m NN0 )
        A. n e. NN0
          (
            (
              A. i e. NN0
                (
                  i <_ n
                  ->
                  ( f ` i ) = ( g ` i )
                )
            )
            ->
            (
              (
                A. m e. NN0
                  (
                    m <_ n
                    ->
                    E. p e. NN0
                      ( p <_ n /\ ( f ` p ) = m )
                  )
              )
              ->
              A. m e. NN0
                (
                  m <_ n
                  ->
                  E. p e. NN0
                    ( p <_ n /\ ( g ` p ) = m )
                )
            )
          )
  $.
$}
