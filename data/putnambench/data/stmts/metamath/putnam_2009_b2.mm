$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2009_b2: the attainable total costs of finite increasing jump
  sequences from zero to one are exactly the reals greater than one third
  and at most one. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  RR ^m NN0 is the class of all real-valued sequences indexed by the
  nonnegative integers. The first two conjuncts require that s starts at zero
  and is strictly increasing on all natural indices, exactly as in the source
  formalizations. The endpoint index n remains internally existential.

  The half-open integer interval 0 ..^ n consists of the indices from zero
  through n - 1, so the finite sum is the total of the source jump costs

    s(i+1)^3 - s(i) * s(i+1)^2.

  The right side is the annotated solution Ioc (1 / 3) 1. The final
  declaration is the single unproved $a corpus statement; this database
  contains no $p proof statement.
$)

${
  $d c i j n s $.

  putnambench-putnam-2009-b2 $a |-
    {
      c e. RR |
      E. s e. ( RR ^m NN0 )
        (
          ( s ` 0 ) = 0
          /\
          (
            A. i e. NN0 A. j e. NN0
              (
                i < j
                ->
                ( s ` i ) < ( s ` j )
              )
            /\
            E. n e. NN0
              (
                ( s ` n ) = 1
                /\
                (
                  sum_ i e. ( 0 ..^ n )
                    (
                      ( ( s ` ( i + 1 ) ) ^ 3 )
                      -
                      (
                        ( s ` i )
                        x.
                        ( ( s ` ( i + 1 ) ) ^ 2 )
                      )
                    )
                )
                =
                c
              )
          )
        )
    }
    =
    {
      c e. RR |
      (
        ( 1 / 3 ) < c
        /\
        c <_ 1
      )
    }
  $.
$}
