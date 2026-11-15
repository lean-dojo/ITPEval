$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1971_a5: characterization of the positive integer score values
  whose nonnegative combinations omit exactly 35 natural scores, including
  58, as the pair (11, 8). This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For integers a and b, the restricted set abstraction is exactly the set
  of natural scores that are not of the form m a + n b for natural m and n.
  Its set.mm cardinality equals 35 exactly when there are 35 such scores;
  the separate existential negation states that 58 is one of them.

  The universal quantifiers and implication render the source's arbitrary
  integer parameters and positivity/order assumption. The final
  biconditional uses the solution pair (11, 8) recorded by both ground-truth
  sources. The declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d a b m n s $.

  putnambench-putnam-1971-a5 $a |-
    A. a e. ZZ A. b e. ZZ
      (
        (
          (
            ( 0 < a /\ 0 < b )
            /\
            b < a
          )
          ->
          (
            (
              (
                # `
                  { s e. NN0 |
                    -. E. m e. NN0 E. n e. NN0
                      ( ( m x. a ) + ( n x. b ) ) = s
                  }
              )
              =
              ; 3 5
              /\
              -. E. m e. NN0 E. n e. NN0
                ( ( m x. a ) + ( n x. b ) ) = ; 5 8
            )
            <->
            (
              a = ; 1 1
              /\
              b = 8
            )
          )
        )
      )
  $.
$}
