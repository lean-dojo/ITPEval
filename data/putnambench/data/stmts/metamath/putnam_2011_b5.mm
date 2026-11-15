$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2011_b5: a uniform linear bound on whole-line integrals of squared
  Cauchy-kernel sums implies a uniform cubic lower bound on the associated
  double sums for an arbitrary real sequence. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The sequence a is an arbitrary NN0-indexed real sequence. For each n, the
  finite interval 0 ..^ n is exactly the zero-based index set with n terms
  used by the primary Lean source. The S. RR binder is set.mm's real
  Lebesgue integral over the whole real line.

  The constants A and positive B remain internally existential, and both
  inequalities are required uniformly for every nonnegative integer n. The
  final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d a c d i j n x $.

  putnambench-putnam-2011-b5 $a |-
    A. a e. ( RR ^m NN0 )
      (
        E. c e. RR
          A. n e. NN0
            S. RR
              (
                (
                  sum_ i e. ( 0 ..^ n )
                    (
                      1
                      /
                      (
                        1
                        +
                        (
                          x
                          -
                          ( a ` i )
                        )
                        ^ 2
                      )
                    )
                )
                ^ 2
              )
              _d x
            <_
            ( c x. n )
        ->
        E. d e. RR
          (
            0 < d
            /\
            A. n e. NN0
              (
                sum_ i e. ( 0 ..^ n )
                  sum_ j e. ( 0 ..^ n )
                    (
                      1
                      +
                      (
                        ( a ` i )
                        -
                        ( a ` j )
                      )
                      ^ 2
                    )
              )
              >_
              (
                d
                x.
                ( n ^ 3 )
              )
          )
      )
  $.
$}
