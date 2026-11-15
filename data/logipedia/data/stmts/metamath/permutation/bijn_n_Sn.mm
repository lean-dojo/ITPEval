$(
  Statement-only formalization of the Logipedia corpus artifact
  permutation.bijn_n_Sn (logipedia__metamath__permutation.bijn_n_Sn),
  catalog title "permutation.bijn_n_Sn": the source-defined bounded-preimage
  property on the natural-number initial segment through n extends through
  successor n when the successor is fixed by the endofunction. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  The shared Coq and Lean module sources define bijn f k exactly as: every
  natural m at most k has a natural preimage p at most k with f(p) = m.
  Injectivity is the separate source predicate injn and is not a conjunct of
  bijn. NN0 and ( NN0 ^m NN0 ) preserve the source natural-number and total
  endofunction domains, and each occurrence of bijn below is unfolded with
  its own bound. The source successor S n is rendered by n + 1, and SetMM's
  native equality bidirectionally represents the source equality predicate.
  The final declaration is an unproved $a statement encoding.
$)

${
  $d f m n p $.

  logipedia-permutation-bijn-n-sn $a |-
    A. f e. ( NN0 ^m NN0 )
      A. n e. NN0
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
          (
            ( f ` ( n + 1 ) ) = ( n + 1 )
            ->
            A. m e. NN0
              (
                m <_ ( n + 1 )
                ->
                E. p e. NN0
                  (
                    p <_ ( n + 1 )
                    /\
                    ( f ` p ) = m
                  )
              )
          )
        )
  $.
$}
