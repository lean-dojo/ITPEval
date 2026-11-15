$(
  Statement-only formalization of PutnamBench artifact putnam_1966_a1:
  the difference of two inclusive partial sums of the sequence
  0, 0, 1, 1, 2, 2, ... equals xy for positive integers x > y.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For an integer index m, floor(m / 2) is definitionally equal to m / 2
  when m is even and to (m - 1) / 2 when m is odd. Thus the lambda below
  is exactly the source function f, including its empty sums at negative
  integer bounds. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof statement.
$)

${
  $d f m n x y $.

  putnambench-putnam-1966-a1 $a |- A. f e. ( ZZ ^m ZZ )
    (
      f =
        (
          n e. ZZ |->
            sum_ m e. ( 0 ... n )
              ( |_ ` ( m / 2 ) )
        )
      ->
      A. x e. ZZ A. y e. ZZ
        (
          (
            (
              0 < x
              /\
              (
                0 < y
                /\
                y < x
              )
            )
            ->
            ( x x. y ) =
              (
                ( f ` ( x + y ) )
                -
                ( f ` ( x - y ) )
              )
          )
        )
    )
  $.
$}
