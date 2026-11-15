$(
  Statement-only formalization of the Logipedia corpus artifact
  permutation.bijn_fg (logipedia__metamath__permutation.bijn_fg), catalog
  title "permutation.bijn_fg": bounded surjectivity on a natural-number
  initial segment is preserved by composition of total natural-number
  endofunctions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 and ( NN0 ^m NN0 ) preserve the source natural-number and total
  endofunction domains. Each occurrence of the source predicate bijn is
  unfolded: every m at most n has a preimage p at most n. SetMM's native
  equality bidirectionally represents the source equality predicate.
  The final declaration is an unproved $a statement encoding.
$)

${
  $d f g m n p $.

  logipedia-permutation-bijn-fg $a |-
    A. f e. ( NN0 ^m NN0 )
      A. g e. ( NN0 ^m NN0 )
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
              (
                A. m e. NN0
                  (
                    m <_ n
                    ->
                    E. p e. NN0
                      ( p <_ n /\ ( g ` p ) = m )
                  )
              )
              ->
              A. m e. NN0
                (
                  m <_ n
                  ->
                  E. p e. NN0
                    (
                      p <_ n
                      /\
                      ( f ` ( g ` p ) ) = m
                    )
                )
            )
          )
  $.
$}
