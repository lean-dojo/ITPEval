$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2011_b2: the primes occurring in at least seven ordered prime
  triples whose associated quadratic has a rational root are exactly
  2 and 5. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The carrier 0 ..^ 3 represents Fin 3, so a member of
  Prime ^m ( 0 ..^ 3 ) is exactly an ordered triple of natural primes.
  The restricted class inlines the source definition of S: its first
  condition retains the internally existential rational root, and its
  second condition says that t occurs in one of the three coordinates.

  SetMM's # assigns +oo to an infinite set, so comparison with 7 agrees
  with Lean's extended-cardinality comparison and with ordinary finite
  cardinality here. The annotated solution set is inlined as { 2 , 5 }.
  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof declaration.
$)

${
  $d i s t x $.

  putnambench-putnam-2011-b2 $a |-
    A. t e. NN0
      (
        (
          t e. Prime
          /\
          7
          <_
          (
            #
            `
            {
              s e. ( Prime ^m ( 0 ..^ 3 ) )
              |
              (
                E. x e. QQ
                  (
                    (
                      (
                        (
                          ( s ` 0 )
                          x.
                          ( x ^ 2 )
                        )
                        +
                        (
                          ( s ` 1 )
                          x.
                          x
                        )
                      )
                      +
                      ( s ` 2 )
                    )
                    =
                    0
                  )
                /\
                E. i e. ( 0 ..^ 3 )
                  ( s ` i ) = t
              )
            }
          )
        )
        <->
        t e. { 2 , 5 }
      )
  $.
$}
