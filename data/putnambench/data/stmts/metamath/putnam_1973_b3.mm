$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1973_b3: a prime-producing quadratic condition determines exactly
  one reduced integer triple with discriminant 1 - 4p.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is the class of nonnegative integers and Prime is the class of natural
  primes. Thus the restricted quantification over x below p is exactly the
  source natural-number range 0 <= x < p.

  A source triple (a,b,c) is represented by set.mm's ordered triple
  <. a , b , c >. = <. <. a , b >. , c >., hence by an element of
  ( ZZ X. ZZ ) X. ZZ. The nested projections recover a, b, and c, so the
  restricted unique existential quantifier states uniqueness of the entire
  integer triple. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof statement.
$)

${
  $d p t x $.

  putnambench-putnam-1973-b3 $a |- A. p e. NN0
    (
      (
        1 < p
        /\
        A. x e. NN0
          (
            x < p
            ->
            ( ( ( x ^ 2 ) - x ) + p ) e. Prime
          )
      )
      ->
      E! t e. ( ( ZZ X. ZZ ) X. ZZ )
        (
          (
            (
              ( 2nd ` ( 1st ` t ) ) ^ 2
            )
            -
            (
              ( 4 x. ( 1st ` ( 1st ` t ) ) )
              x.
              ( 2nd ` t )
            )
          )
          =
          ( 1 - ( 4 x. p ) )
          /\
          (
            0 < ( 1st ` ( 1st ` t ) )
            /\
            (
              ( 1st ` ( 1st ` t ) ) <_ ( 2nd ` t )
              /\
              (
                ( -u ( 1st ` ( 1st ` t ) ) )
                <_
                ( 2nd ` ( 1st ` t ) )
                /\
                ( 2nd ` ( 1st ` t ) )
                <
                ( 1st ` ( 1st ` t ) )
              )
            )
          )
        )
    )
  $.
$}
