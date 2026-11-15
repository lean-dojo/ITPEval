$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1972_a6: an integrable real function on the unit interval with
  vanishing lower moments and normalized nth moment has the stated large
  absolute-value bound on a set of positive measure. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  The function F is an arbitrary total real-valued function on the reals;
  membership of its restriction to [0,1] in L^1 is the source integrability
  assumption. The finite interval 0 ..^ n consists exactly of the
  nonnegative integer exponents strictly below n. All interval integrals are
  Lebesgue integrals on [0,1].

  The witness S is internally existential, is a Lebesgue-measurable subset of
  [0,1], and has strictly positive Lebesgue measure. The final declaration is
  the single unproved $a corpus statement; this database contains no $p proof
  statement.
$)

${
  $d F S i n x $.

  putnambench-putnam-1972-a6 $a |-
    A. F e. ( RR ^m RR )
    A. n e. NN0
      (
        (
          ( x e. ( 0 [,] 1 ) |-> ( F ` x ) ) e. L^1
          /\
          (
            A. i e. ( 0 ..^ n )
              (
                S. ( 0 [,] 1 )
                  (
                    ( x ^ i )
                    x.
                    ( F ` x )
                  )
                  _d x
              )
              =
              0
            /\
            (
              S. ( 0 [,] 1 )
                (
                  ( x ^ n )
                  x.
                  ( F ` x )
                )
                _d x
            )
            =
            1
          )
        )
        ->
        E. S e. dom vol
          (
            S C_ ( 0 [,] 1 )
            /\
            (
              0 < ( vol ` S )
              /\
              A. x e. S
                (
                  ( 2 ^ n )
                  x.
                  ( n + 1 )
                )
                <_
                ( abs ` ( F ` x ) )
            )
          )
      )
  $.
$}
