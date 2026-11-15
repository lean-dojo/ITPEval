$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2014_a4: the smallest probability at zero for a nonnegative
  integer-valued random variable with first three moments 1, 2, and 5 is
  1 / 3. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A probability law on the nonnegative integers is represented by a real
  sequence x indexed by NN0. The pointwise interval condition and the first
  unbounded sum say that its entries are probabilities with total mass one.
  The next three unbounded sums are exactly the first, second, and third
  moments of the associated nonnegative integer-valued random variable.

  The first conjunct gives the lower bound 1 / 3 for every admissible law.
  The second retains an internally existential admissible law attaining that
  value. Together these say exactly that 1 / 3 is the smallest possible
  probability of X = 0. The final declaration is the single unproved $a
  corpus statement; this database contains no $p proof declaration.
$)

${
  $d i x y $.

  putnambench-putnam-2014-a4 $a |-
    (
      A. x e. ( RR ^m NN0 )
        (
          (
            (
              A. i e. NN0
                (
                  0 <_ ( x ` i )
                  /\
                  ( x ` i ) <_ 1
                )
              /\
              (
                sum_ i e. NN0
                  ( x ` i )
              )
              =
              1
            )
            /\
            (
              (
                sum_ i e. NN0
                  ( i x. ( x ` i ) )
              )
              =
              1
              /\
              (
                (
                  sum_ i e. NN0
                    ( ( i ^ 2 ) x. ( x ` i ) )
                )
                =
                2
                /\
                (
                  sum_ i e. NN0
                    ( ( i ^ 3 ) x. ( x ` i ) )
                )
                =
                5
              )
            )
          )
          ->
          ( 1 / 3 ) <_ ( x ` 0 )
        )
      /\
      E. y e. ( RR ^m NN0 )
        (
          (
            (
              A. i e. NN0
                (
                  0 <_ ( y ` i )
                  /\
                  ( y ` i ) <_ 1
                )
              /\
              (
                sum_ i e. NN0
                  ( y ` i )
              )
              =
              1
            )
            /\
            (
              (
                sum_ i e. NN0
                  ( i x. ( y ` i ) )
              )
              =
              1
              /\
              (
                (
                  sum_ i e. NN0
                    ( ( i ^ 2 ) x. ( y ` i ) )
                )
                =
                2
                /\
                (
                  sum_ i e. NN0
                    ( ( i ^ 3 ) x. ( y ` i ) )
                )
                =
                5
              )
            )
          )
          /\
          ( y ` 0 ) = ( 1 / 3 )
        )
    )
  $.
$}
