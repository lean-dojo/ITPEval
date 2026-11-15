$(
  Statement-only formalization of Thousand Theorems corpus artifact Q132469
  (thousand-theorems__metamath__Q132469), "Fermat's Last Theorem": for every
  natural exponent at least three, no three nonzero natural numbers satisfy
  the corresponding Fermat equation. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN0 is the class of natural numbers including zero. The conjunction
  of the three nonzero conditions is propositionally equivalent to the
  source's three successive hypotheses. The declaration below is the single
  unproved $a corpus statement; this root artifact contains no $p proof
  declaration.
$)

${
  $d a b c n $.

  thousand-theorems-q132469-fermat-last-theorem $a |-
    A. n e. NN0
      (
        3 <_ n
        ->
        A. a e. NN0
          A. b e. NN0
            A. c e. NN0
              (
                (
                  a =/= 0
                  /\
                  (
                    b =/= 0
                    /\
                    c =/= 0
                  )
                )
                ->
                (
                  ( ( a ^ n ) + ( b ^ n ) )
                  =/=
                  ( c ^ n )
                )
              )
      )
  $.
$}
