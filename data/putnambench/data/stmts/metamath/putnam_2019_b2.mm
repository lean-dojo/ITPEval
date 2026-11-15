$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2019_b2: evaluation of the normalized cubic-growth limit of a
  finite trigonometric sum as 8 divided by pi cubed. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  The sequence is indexed by the positive integers, exactly the n >= 1
  domain in the published problem. This is a tail of the natural-indexed
  sequences in the Lean and Isabelle sources, so it has the same limit at
  infinity while avoiding the irrelevant expression at n = 0.

  The summand follows the published problem and the primary Lean and
  Isabelle sources, with sine argument (2k - 1) pi / (2n). The Rocq source's
  different sine numerator is an evident transcription error; its explicit
  solution 8 / pi^3 agrees with the solution annotations in the primary
  sources. SetMM's trigonometric and arithmetic operations are complex-valued,
  but every displayed value is real, and complex sequence convergence on
  these values is equivalent to the source real convergence.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof declaration.
$)

${
  $d k n $.

  putnambench-putnam-2019-b2 $a |-
    (
      n e. NN |->
        (
          (
            sum_ k e. ( 1 ... ( n - 1 ) )
              (
                (
                  sin
                  `
                  (
                    (
                      ( ( 2 x. k ) - 1 )
                      x.
                      _pi
                    )
                    /
                    ( 2 x. n )
                  )
                )
                /
                (
                  (
                    (
                      cos
                      `
                      (
                        (
                          ( k - 1 )
                          x.
                          _pi
                        )
                        /
                        ( 2 x. n )
                      )
                    )
                    ^ 2
                  )
                  x.
                  (
                    (
                      cos
                      `
                      (
                        ( k x. _pi )
                        /
                        ( 2 x. n )
                      )
                    )
                    ^ 2
                  )
                )
              )
          )
          /
          ( n ^ 3 )
        )
    )
    ~~>
    ( 8 / ( _pi ^ 3 ) )
  $.
$}
