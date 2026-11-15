$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2006_a5: the ratio of the sum to the product of the tangent
  values tan(theta + k*pi/n), for odd positive n and irrational theta/pi,
  equals n or -n according to n modulo four. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN and Odd restrict n to the positive odd integers. The class
  RR ^m ( 1 ... n ) contains exactly the real-valued functions on the
  source index interval. Nonmembership of t / _pi in QQ is precisely the
  irrationality assumption on theta / pi.

  The finite sum and product use the same inclusive interval 1 ... n.
  The conditional inlines the explicit source solution: n when n is
  congruent to one modulo four, and -n otherwise. The final declaration
  is the single unproved $a corpus statement; this database contains no
  $p proof statement.
$)

${
  $d a k n t $.

  putnambench-putnam-2006-a5 $a |-
    A. n e. NN
      A. t e. RR
        A. a e. ( RR ^m ( 1 ... n ) )
          (
            (
              (
                n e. Odd
                /\
                ( t / _pi ) e/ QQ
              )
              /\
              A. k e. ( 1 ... n )
                ( a ` k )
                =
                (
                  tan
                  `
                  (
                    t
                    +
                    (
                      ( k x. _pi )
                      /
                      n
                    )
                  )
                )
            )
            ->
            (
              (
                sum_ k e. ( 1 ... n )
                  ( a ` k )
              )
              /
              (
                prod_ k e. ( 1 ... n )
                  ( a ` k )
              )
            )
            =
            if (
              ( n mod 4 ) = 1 ,
              n ,
              ( -u n )
            )
          )
  $.
$}
