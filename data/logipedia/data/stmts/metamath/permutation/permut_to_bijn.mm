$(
  Statement-only formalization of the Logipedia corpus artifact
  permutation.permut_to_bijn
  (logipedia__metamath__permutation.permut_to_bijn), catalog title
  "permutation.permut_to_bijn": every natural-number endofunction that maps
  an inclusive initial segment into itself and is injective there is
  surjective on that segment. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 and ( NN0 ^m NN0 ) preserve the source natural-number and total
  endofunction domains. The antecedent directly unfolds permutation.permut
  as closure on the inclusive initial segment through n together with
  injectivity on that segment. The conclusion directly unfolds
  permutation.bijn: every m at most n has a preimage p at most n. Restricted
  quantifiers, implications, conjunctions, and SetMM equality preserve the
  source binder order, assumptions, and conclusion. The final declaration is
  Metamath's native unproved $a statement encoding; this artifact adds no $p
  proof declaration.
$)

${
  $d f i j m n p $.

  logipedia-permutation-permut-to-bijn $a |-
    A. n e. NN0
      A. f e. ( NN0 ^m NN0 )
        (
          (
            (
              A. i e. NN0
                (
                  i <_ n
                  ->
                  ( f ` i ) <_ n
                )
            )
            /\
            A. i e. NN0
              A. j e. NN0
                (
                  i <_ n
                  ->
                  (
                    j <_ n
                    ->
                    (
                      ( f ` i ) = ( f ` j )
                      ->
                      i = j
                    )
                  )
                )
          )
          ->
          A. m e. NN0
            (
              m <_ n
              ->
              E. p e. NN0
                ( p <_ n /\ ( f ` p ) = m )
            )
        )
  $.
$}
