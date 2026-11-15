$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1986_b4: the minimum distance from a real number to values
  sqrt(m^2 + 2 n^2), for integers m and n, tends to zero as the real
  number tends to positive infinity. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  G ranges over total real-valued functions on the reals. The first
  hypothesis says that G(r) is attained by some integer pair (m,n), and the
  second says that it is a lower bound for the corresponding distance for
  every integer pair. Together these state exactly that G(r) is the source
  minimum for every real r.

  Set.mm's complex modulus abs agrees with real absolute value here, and its
  principal square root is applied to the nonnegative real integer expression
  m^2 + 2 n^2. The relation ~~>r is the limit at positive infinity for a
  real-indexed function. The Rocq ground truth defines the solution predicate
  as True, so its biconditional is equivalent to this limit assertion.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d G m n r $.

  putnambench-putnam-1986-b4 $a |- A. G e. ( RR ^m RR )
    (
      (
        A. r e. RR
          E. m e. ZZ E. n e. ZZ
            (
              ( G ` r )
              =
              (
                abs
                `
                (
                  r
                  -
                  (
                    sqrt
                    `
                    (
                      ( m ^ 2 )
                      +
                      ( 2 x. ( n ^ 2 ) )
                    )
                  )
                )
              )
            )
        /\
        A. r e. RR A. m e. ZZ A. n e. ZZ
          (
            ( G ` r )
            <_
            (
              abs
              `
              (
                r
                -
                (
                  sqrt
                  `
                  (
                    ( m ^ 2 )
                    +
                    ( 2 x. ( n ^ 2 ) )
                  )
                )
              )
            )
          )
      )
      ->
      G ~~>r 0
    )
  $.
$}
