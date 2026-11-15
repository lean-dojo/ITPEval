$(
  Statement-only formalization of PutnamBench artifact putnam_1963_a4:
  the extended-real limsup bound for a sequence of positive real numbers,
  together with the sharpness of the constant one. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  The set.mm function limsup takes values in the extended reals RR*, so an
  unbounded-above real sequence has the same plus-infinity behavior represented
  explicitly by the auxiliary predicates in the Lean and Rocq sources.

  The final unproved $a assertion quantifies over every positive real sequence.
  Its second conjunct preserves the internal counterexample sequence for each
  real constant greater than one.
$)

${
  $d A C n $.

  putnambench-putnam-1963-a4 $a |- (
    A. A e. ( RR ^m NN0 )
      (
        A. n e. NN0 0 < ( A ` n )
        ->
        1 <_
          (
            limsup
            `
            (
              n e. NN0 |->
                (
                  n
                  x.
                  (
                    (
                      ( 1 + ( A ` ( n + 1 ) ) )
                      /
                      ( A ` n )
                    )
                    -
                    1
                  )
                )
            )
          )
      )
    /\
    A. C e. RR
      (
        1 < C
        ->
        E. A e. ( RR ^m NN0 )
          (
            A. n e. NN0 0 < ( A ` n )
            /\
            -.
              C <_
                (
                  limsup
                  `
                  (
                    n e. NN0 |->
                      (
                        n
                        x.
                        (
                          (
                            ( 1 + ( A ` ( n + 1 ) ) )
                            /
                            ( A ` n )
                          )
                          -
                          1
                        )
                      )
                  )
                )
          )
      )
  ) $.
$}
