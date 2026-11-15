$(
  Statement-only formalization of the Logipedia corpus artifact
  permutation.injn_Sn_n (logipedia__metamath__permutation.injn_Sn_n),
  catalog title "permutation.injn_Sn_n": injectivity of a natural-number
  endofunction on the initial segment through successor n implies injectivity
  on the initial segment through n. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 and ( NN0 ^m NN0 ) preserve the source natural-number and total
  endofunction domains. Each occurrence of the source predicate injn is
  unfolded as equality reflection for arbitrary natural indices at most the
  stated bound. The source successor S n is rendered by n + 1, and SetMM's
  native equality bidirectionally represents the source equality predicate
  on natural numbers. The restricted quantifiers and nested implications
  preserve the source binder and assumption scopes. The final declaration is
  Metamath's native unproved $a statement encoding; this artifact adds no $p
  proof declaration.
$)

${
  $d f i j n $.

  logipedia-permutation-injn-sn-n $a |-
    A. f e. ( NN0 ^m NN0 )
      A. n e. NN0
        (
          (
            A. i e. NN0
              A. j e. NN0
                (
                  i <_ ( n + 1 )
                  ->
                  (
                    j <_ ( n + 1 )
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
  $.
$}
