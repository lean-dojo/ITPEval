$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2023_a5: the complex zeros of the finite polynomial sum weighted
  by the number of ones in each index's base-3 expansion are the three
  specified complex numbers. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is set.mm's class of nonnegative integers and CC is its complex
  plane. The universally quantified function d is characterized by the
  ternary recurrence d(0) = 0 and, for positive n, d(n) is the indicator
  that n mod 3 equals 1 plus d(floor(n/3)). This is exactly the number of
  ones in the usual base-3 expansion.

  The restricted class on the left is the full complex zero set of the
  source finite sum. The three-element class on the right inlines the
  solution annotation from the Lean and Isabelle ground truth, with _i
  denoting the imaginary unit and sqrt the nonnegative real square root.
  The final declaration is a single unproved $a corpus statement; this
  database contains no $p proof declaration.
$)

${
  $d d k n z $.

  putnambench-putnam-2023-a5 $a |-
    A. d e. ( NN0 ^m NN0 )
      (
        A. n e. NN0
          ( d ` n )
          =
          if (
            n = 0 ,
            0 ,
            (
              if (
                ( n mod 3 ) = 1 ,
                1 ,
                0
              )
              +
              ( d ` ( |_ ` ( n / 3 ) ) )
            )
          )
        ->
        {
          z e. CC |
          (
            sum_ k e.
              (
                0
                ...
                (
                  ( 3 ^ ( ; ; ; 1 0 1 0 ) )
                  -
                  1
                )
              )
              (
                ( ( -u 2 ) ^ ( d ` k ) )
                x.
                (
                  ( z + k )
                  ^
                  ( ; ; ; 2 0 2 3 )
                )
              )
          )
          =
          0
        }
        =
        {
          (
            -u
            (
              (
                ( 3 ^ ( ; ; ; 1 0 1 0 ) )
                -
                1
              )
              /
              2
            )
          ) ,
          (
            (
              -u
              (
                (
                  ( 3 ^ ( ; ; ; 1 0 1 0 ) )
                  -
                  1
                )
                /
                2
              )
            )
            +
            (
              (
                (
                  sqrt
                  `
                  (
                    ( 9 ^ ( ; ; ; 1 0 1 0 ) )
                    -
                    1
                  )
                )
                x.
                _i
              )
              /
              4
            )
          ) ,
          (
            (
              -u
              (
                (
                  ( 3 ^ ( ; ; ; 1 0 1 0 ) )
                  -
                  1
                )
                /
                2
              )
            )
            -
            (
              (
                (
                  sqrt
                  `
                  (
                    ( 9 ^ ( ; ; ; 1 0 1 0 ) )
                    -
                    1
                  )
                )
                x.
                _i
              )
              /
              4
            )
          )
        }
      )
  $.
$}
